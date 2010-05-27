(*
 * Copyright © 2009 The Regents of the University of California. All rights reserved. 
 *
 * Permission is hereby granted, without written agreement and without 
 * license or royalty fees, to use, copy, modify, and distribute this 
 * software and its documentation for any purpose, provided that the 
 * above copyright notice and the following two paragraphs appear in 
 * all copies of this software. 
 * 
 * IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY 
 * FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES 
 * ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN 
 * IF THE UNIVERSITY OF CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY 
 * OF SUCH DAMAGE. 
 * 
 * THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES, 
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY 
 * AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS 
 * ON AN "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION 
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
 *)

module Sy = Ast.Symbol
module P  = Ast.Predicate 
module C  = FixConstraint
open Misc.Ops

(************************************************************************)
(********************* Build Graph of Kvar Dependencies *****************)
(************************************************************************)

module V : Graph.Sig.COMPARABLE with type t = C.refa = struct
  type t = C.refa
  let hash    = C.refa_to_string <+> Hashtbl.hash
  let compare = fun x y -> compare (C.refa_to_string x) (C.refa_to_string y)
  let equal   = fun x y -> C.refa_to_string x = C.refa_to_string y
end

module Id : Graph.Sig.ORDERED_TYPE_DFT with type t = int = struct
  type t = int
  let default = 0
  let compare = compare
end

module G   = Graph.Imperative.Digraph.ConcreteLabeled(V)(Id)
module VS  = Set.Make(V)

type t = G.t

(************************************************************************)
(*************************** Dumping to Dot *****************************) 
(************************************************************************)

module DotGraph = struct
  type t = G.t
  module V = G.V
  module E = G.E
  let iter_vertex               = G.iter_vertex
  let iter_edges_e              = G.iter_edges_e
  let graph_attributes          = fun _ -> [`Size (11.0, 8.5); `Ratio (`Float 1.29)]
  let default_vertex_attributes = fun _ -> [`Shape `Box]
  let vertex_name               = function C.Kvar (_,k) -> Sy.to_string k | ra -> "C"^(string_of_int (V.hash ra))
  let vertex_attributes         = fun ra -> [`Label (C.refa_to_string ra)] 
  let default_edge_attributes   = fun _ -> []
  let edge_attributes           = fun (_,i,_) -> [`Label (string_of_int i)]
  let get_subgraph              = fun _ -> None
end

module Dot = Graph.Graphviz.Dot(DotGraph) 

let dump_graph s g = 
  s |> open_out 
    >> (fun oc -> Dot.output_graph oc g)
    |> close_out 

(************************************************************************)
(********************* Constraints-to-Graph *****************************) 
(************************************************************************)

let kvars_of_env env = 
  Sy.SMap.fold begin fun _ r ks -> 
    r |> C.kvars_of_reft |> (fun lks -> lks ++ ks)
  end env []

let edges_of_t c =
  let eks = c |> C.env_of_t 
              |> kvars_of_env 
              |> List.map (fun (_,k) -> C.Kvar ([], k)) in
  let gps = c |> C.grd_of_t 
              |> (fun p -> if P.is_tauto p then [] else [C.Conc p]) in
  let lks = c |> C.lhs_of_t 
              |> C.ras_of_reft in 
  let rs  = c |> C.rhs_of_t 
              |> C.ras_of_reft 
              |> List.map (function C.Kvar (_,k) -> C.Kvar ([], k) | ra -> ra) in
  rs |> Misc.cross_product (lks ++ gps ++ eks)  
     |> List.map (fun (ra, ra') -> (ra, C.id_of_t c, ra'))

(* API *)
let create cs =
  G.create ()
  >> (fun g -> List.iter ((List.iter (G.add_edge_e g)) <.> edges_of_t) cs)
  >> dump_graph (!Constants.save_file^".dot")

(************************************************************************)
(*************************** Misc. Accessors ****************************) 
(************************************************************************)

let vertices_of_graph = fun g -> G.fold_vertex (fun v acc -> v::acc) g []
let kvaro_of_refa     = function C.Kvar (_,k) -> Some k | _ -> None

(************************************************************************)
(********************* (Backwards) Reachability *************************) 
(************************************************************************)

let vset_of_list vs = List.fold_left (fun s v -> VS.add v s) VS.empty vs
let pre_star g vs =
  (vs, VS.empty)
  |> Misc.fixpoint begin function 
     | [], r -> ([], r), false
     | ws, r -> ws |> List.filter (fun v -> not (VS.mem v r)) 
                   |> Misc.tmap2 (Misc.flap (G.pred g), vset_of_list <+> VS.union r)
                   |> (fun x -> x, true) 
     end 
  |> fst |> snd 
  |> VS.elements

(************************************************************************)
(********************************* API **********************************) 
(************************************************************************)

let filter_kvars f g =
  g |> vertices_of_graph
    |> List.filter (not <.> C.is_conc_refa)
    |> List.filter f 
    |> Misc.map_partial kvaro_of_refa 

let is_num_write g f v = 
  v |> G.pred_e g
    |> List.map snd3
    |> Misc.sort_and_compact
    |> List.length 
    |> f

let single_write_kvars g =
  filter_kvars (is_num_write g ((=) 1)) g

let undefined_kvars g =
  filter_kvars (is_num_write g ((=) 0)) g

let multi_write_kvars g =
  filter_kvars (is_num_write g ((<) 1)) g
 
let cone_kvars g = 
  g |> vertices_of_graph
    |> List.filter C.is_conc_refa
    |> pre_star g
    |> List.filter (not <.> C.is_conc_refa)
    |> Misc.map_partial kvaro_of_refa 

(*************************************************************************)
(******************* For now, a single function API **********************)
(*************************************************************************)

let print_ks s ks = 
  Format.printf "[KVG] %s %a \n" s 
  (Misc.pprint_many false "," Sy.print) ks

let kv_stats cs = 
  cs |> create
     >> (single_write_kvars <+> print_ks "single write kvs:")
     >> (multi_write_kvars  <+> print_ks "multi write kvs:")
     >> (undefined_kvars    <+> print_ks "undefined kvs:")
     >> (cone_kvars         <+> print_ks "cone kvs:")
     |> ignore
