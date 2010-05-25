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

module SM = Misc.StringMap
module C  = FixConstraint
open Misc.Ops

(************************************************************************)
(********************* Build Graph of Kvar Dependencies *****************)
(************************************************************************)

module K : Graph.Sig.COMPARABLE with type t = C.refa = struct
  type t = C.refa
  let hash    = C.refa_to_string <+> Hashtbl.hash
  let compare = fun x y -> compare (C.refa_to_string x) (C.refa_to_string)
  let equal   = fun x y -> equal (C.refa_to_string x) (C.refa_to_string y)
end

module I : Graph.Sig.ORDERED_TYPE_DFT with type t = int = struct
  type t = int
  let compare = compare
end

module G   = Graph.Imperative.Digraph.ConcreteLabeled(K)(I)

type t = G.t

(************************************************************************)
(********************* Constraints-to-Graph *****************************) 
(************************************************************************)

let kvars_of_env env = 
  Sy.SMap.fold begin fun _ r ks -> 
    r |> C.kvars_of_reft |> (fun lks -> lks ++ ks)
  end env []

let edges_of_t c =
  let lks = c |> C.env_of_t 
              |> kvars_of_env 
              |> List.map (fun (_,k) -> C.Kvar ([], k)) in
  let lps = c |> C.grd_of_t 
              |> (fun p -> if P.is_tauto p then [] else [p]) in
  let rs  = c |> C.rhs_of_t 
              |> C.ras_of_reft 
              |> List.map (fun C.Kvar (_,k) -> C.Kvar ([], k) | ra -> ra) in
  rs |> Misc.cross_product (lps ++ lks)  
     |> List.map (fun (ra, ra') -> (ra, C.id_of_t c, ra'))

(* API *)
let create cs =
  let g = G.create () in
  let _ = List.iter ((List.iter (G.add_edge g)) <.> edges_of_t) cs in
  g

(************************************************************************)
(*************************** Misc. Accessors ****************************) 
(************************************************************************)

let vertices_of_graph = fun g -> G.fold_vertex (fun v acc -> v::acc) g []
let kvars_of_graph    = vertices_of_graph <+> List.filter (not <+> C.is_conc_refa)
let concs_of_graph    = vertices_of_graph <+> List.filter is_conc_refa
let kvaro_of_refa     = function C.Kvar (_,k) -> Some k | _ -> None

(************************************************************************)
(********************* (Backwards) Reachability *************************) 
(************************************************************************)

let pre_star g vs = 
  let pre = function 
    | ([], pm) -> 
        false, ([], pm) 
    | (vs, pm) -> 
        let pm' = List.fold_left (fun pm -> SM.add (C.refa_to_string v) v pm) pm vs in
        let vs' = vs |> Misc.flap (G.pred g) 
                     |> List.filter (fun v -> not (SM.mem (C.refa_to_string v) pm)) in
        true, (vs', pm')
  in (vs, SM.empty) |> Misc.fixpoint pre |> snd |> Misc.sm_to_range 

(************************************************************************)
(********************************* API **********************************) 
(************************************************************************)

let single_write_kvars g = 
  g |> kvars_of_graph 
    |> List.filter (fun v -> match G.pred g v with [_] -> true | _ -> false)
    |> Misc.map_partial kvaro_of_refa 

let undefined_kvars g = 
  g |> kvars_of_graph 
    |> List.filter (fun v -> match G.pred g v with [] -> true | _ -> false)
    |> Misc.map_partial kvaro_of_refa 

let cone_kvars g = 
  g |> concs_of_graph 
    |> pre_star g
    |> List.filter (not <+> C.is_conc_refa)
    |> Misc.map_partial kvaro_of_refa 
    

