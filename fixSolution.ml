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

 
(*************************************************************)
(******************** Solution Management ********************)
(*************************************************************)

module F   = Format
module A   = Ast
module E   = A.Expression
module P   = A.Predicate

module Q   = A.Qualifier
module Sy  = A.Symbol
module Su  = A.Subst
module SM  = Sy.SMap
module SSM = Misc.StringMap
module BS  = BNstats
module TP  = TpNull.Prover
module Co  = Constants
open Misc.Ops

let mydebug = false 

let tag_of_qual = snd <.> Q.pred_of_t

module V : Graph.Sig.COMPARABLE with type t = Q.t = struct
  type t = Q.t
  let hash    = tag_of_qual <+> Hashtbl.hash
  let compare = fun q1 q2 -> compare (tag_of_qual q1) (tag_of_qual q2)
  let equal   = fun q1 q2 -> tag_of_qual q1 = tag_of_qual q2
end

module Id : Graph.Sig.ORDERED_TYPE_DFT with type t = unit = struct
  type t = unit 
  let default = ()
  let compare = compare 
end

module G   = Graph.Persistent.Digraph.ConcreteLabeled(V)(Id)
module SCC = Graph.Components.Make(G)

exception UnmappedKvar of Sy.t

module TTM = Map.Make (struct
    type t = A.tag * A.tag 
    let compare = compare 
  end)

type def = Ast.pred * (Ast.Qualifier.t * Ast.Subst.t)

type p   = Sy.t * def

type t   = { m    : def list SM.t
           ; qm   : (Q.t * int) SSM.t (* name :-> (qualif, rank) *)
           ; impm : bool TTM.t       (* (t1,t2) \in impm iff q1 => q2 /\ t1 = tag_of_qual q1 /\ t2 = tag_of_qual q2 *)
           ; impg : G.t              (* same as impm but in graph format *) 
           }

(*************************************************************)
(************* Constructing Initial Solution *****************)
(*************************************************************)


let def_of_pred_qual (p, q) =
  let qp = Q.pred_of_t q in
  match A.unify_pred qp p with
  | Some su -> (p, q, su)
  | None    -> assertf "ERROR: unify q=%s p=%s" (P.to_string qp) (P.to_string p)

let map_of_bindings bs =
  List.fold_left (fun s (k, ds) -> SM.add k ds s) SM.empty bs 

let quals_of_bindings bs =
  bs |> Misc.flap snd
     |> Misc.map (snd <+> fst) 
     |> Misc.sort_and_compact


(************************************************************************)
(*************************** Dumping to Dot *****************************) 
(************************************************************************)


module DotGraph = struct
  type t = G.t
  module V = G.V
  module E = G.E
  let iter_vertex               = G.iter_vertex
  let iter_edges_e              = G.iter_edges_e
  let graph_attributes          = fun _ -> [`Size (11.0, 8.5); `Ratio (`Fill (* Float 1.29*))]
  let default_vertex_attributes = fun _ -> [`Shape `Box]
  let vertex_name               = Q.name_of_t 
  let vertex_attributes         = fun q -> [`Label ((Misc.fsprintf Q.print q))] 
  let default_edge_attributes   = fun _ -> []
  let edge_attributes           = fun (_,(),_) -> [] 
  let get_subgraph              = fun _ -> None
end

module Dot = Graph.Graphviz.Dot(DotGraph) 

let dump_graph s g = 
  s |> open_out 
    >> (fun oc -> Dot.output_graph oc g)
    |> close_out 

(************************************************************)
(***************** Build Implication Graph ******************)
(************************************************************)

let check_tp tp sm q qs = 
  let vv  = Q.vv_of_t q in
  let lps = [Q.pred_of_t q] in
  qs |> List.map (fun q -> ((q, tag_of_qual q), Q.pred_of_t q))
     |> TP.set_filter tp sm vv lps (fun _ _ -> false) 

let cluster_quals = Misc.groupby Q.sort_of_t 

let update_impm_for_quals tp sm impmg qs = 
  List.fold_left begin fun impmg q ->
    let tag   = tag_of_qual q in 
    qs |> check_tp tp sm q 
       |> List.fold_left begin fun (ttm, g) (q', tag') -> 
           ( TTM.add (tag, tag') true ttm
           , G.add_edge_e g (q, (), q'))
          end impmg
  end impmg qs

let close_env =
  List.fold_left begin fun sm x -> 
    if SM.mem x sm 
    then sm 
    else SM.add x Ast.Sort.t_int sm
  end

let impm_of_quals ts sm ps qs =
  let sm = qs |> Misc.flap (Q.pred_of_t <+> P.support) |> close_env sm in
  let tp = TP.create ts sm ps in
  qs |> cluster_quals 
     |> List.fold_left (update_impm_for_quals tp sm) (TTM.empty, G.empty)

let qual_ranks_of_impg impg = 
  let a = SCC.scc_array impg in
  Misc.array_fold_lefti begin fun i qm qs ->
    List.fold_left begin fun qm q ->
      SSM.add (Q.name_of_t q) (q, i) qm
    end qm qs
  end SSM.empty a 

let rank_of_qual s = 
  Q.name_of_t
  <+> Misc.do_catchf "rank_of_qual" (Misc.flip SSM.find s.qm)
  <+> snd


(************************************************************)
(*********************** Profile/Stats **********************)
(************************************************************)

let pprint_ps = Misc.pprint_many false ";" P.print 

(* API *)
let print ppf s =
  SM.to_list s.m 
  |> List.map fst 
  >> List.iter begin fun k ->
       F.fprintf ppf "//solution: %a := [%a] \n"  Sy.print k pprint_ps (read s k)
     end 
  >> List.iter begin fun k ->
       F.fprintf ppf "solution: %a := [%a] \n"  Sy.print k pprint_ds (p_read s k)
     end
  |> ignore
       
(* API *)
let print_stats ppf s =
  let (sum, max, min, bot) =   
    (SM.fold (fun _ qs x -> (+) x (List.length qs)) s.m 0,
     SM.fold (fun _ qs x -> max x (List.length qs)) s.m min_int,
     SM.fold (fun _ qs x -> min x (List.length qs)) s.m max_int,
     SM.fold (fun _ qs x -> x + (if List.exists (fst <+> P.is_contra) qs then 1 else 0)) s.m 0) in
  let n   = Sy.sm_length s.m in
  let avg = (float_of_int sum) /. (float_of_int n) in
  F.fprintf ppf "# Vars: (Total=%d, False=%d) Quals: (Total=%d, Avg=%f, Max=%d, Min=%d)\n" 
    n bot sum avg max min

(* API *)
let save fname s =
  let oc  = open_out fname in
  let ppf = F.formatter_of_out_channel oc in
  F.fprintf ppf "@[%a@] \n" print s;
  close_out oc

let key_of_quals qs = 
  qs |> List.map P.to_string 
     |> List.sort compare
     |> String.concat ","

(* API *)
let dump_cluster s = 
  s.m 
  |> Sy.sm_to_list 
  |> List.map (snd <+> List.map fst)
  |> Misc.groupby key_of_quals
  |> List.map begin function 
     | [] -> assertf "impossible" 
     | (ps::_ as pss) -> Co.cprintf Co.ol_solve 
                         "SolnCluster: preds %d = size %d \n"
                         (List.length ps) (List.length pss)
     end
  |> ignore

(************************************************************)
(*************************** API ****************************)
(************************************************************)

(* API *)
let of_bindings ts sm ps bs =
  let m      = map_of_bindings bs in
  let qs     = quals_of_bindings bs in
  let im, ig = impm_of_quals ts sm ps qs in
  let _      = dump_graph (!Constants.save_file^".impg.dot") ig in
  let qm     = qual_ranks_of_impg ig in 
  {m = m; qm = qm; impm = im; impg = ig}

(* API *)
let empty = of_bindings [] SM.empty [] [] 

(* API *)
let p_read s k =
  let _ = asserts (SM.mem k s.m) "ERROR: p_read : unknown kvar %s\n" (Sy.to_string k) in
  SM.find k s.m 
  |> List.map (fun d -> ((k,d), fst d))
  |> Misc.fsort (fun ((_,(_,(q,_))),_) -> rank_of_qual s q)
  |> List.rev

(* API *)
let p_imp s (_, (p1, (q1, su1)))  (_, (p2, (q2, su2))) =
  su1 = su2 &&  (Misc.map_pair tag_of_qual (q1, q2) |> Misc.flip TTM.mem s.impm) 


let minimize s = Misc.cov_filter (fun x y -> p_imp s (fst x) (fst y)) (fun _ -> true)

(* API *)
let read s k = 
  p_read s k 
  |> (!Constants.minquals <?> minimize s) 
  |> List.map snd


(* INV: qs' \subseteq qs *)
let update m k ds' =
  let ds  = SM.find k m in
  (if mydebug then 
    ds |> List.filter (fun d -> not (List.mem d ds'))
       |> List.map fst
       |> F.printf "Dropping %a: (%d) %a \n" Sy.print k (List.length ds) pprint_ps
  );
  (not (Misc.same_length ds ds'), SM.add k ds' m)


(* API *)
let p_update s0 ks kds = 
  Misc.kgroupby fst kds 
  |> List.fold_left begin fun (b, m) (k, ds) -> 
      ds |> List.map snd 
         |> update m k 
         |> Misc.app_fst ((||) b)
     end (false, s0.m) 
  |> Misc.app_snd (fun m -> { s0 with m = m })  

(* {{{ DEPRECATED 

let read s k = 
  try SM.find k s.m with Not_found -> begin
    Printf.printf "ERROR: Solution.read : unknown kvar %s \n" 
    (Sy.to_string k);
    raise (UnmappedKvar k)
  end


let query s k =
  try SM.find k s with Not_found -> []

let add s k qs' = 
  let qs   = query s k in
  let qs'' = qs' ++ qs in
  (not (Misc.same_length qs qs''), SM.add k qs'' s)

let merge s1 s2 =
  SM.fold (fun k qs s -> add s k qs |> snd) s1 s2 

let map_of_bindings (bs : (Sy.t * def list) list) =
  bs |> List.map (fun (k, defs) -> (k, List.map fst defs)) 
     |> List.fold_left (fun s (k, ps) -> SM.add k ps s) SM.empty 
  
  }}} *)
