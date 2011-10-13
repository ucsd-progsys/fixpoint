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
module C   = FixConstraint

module SSM = Misc.StringMap
module BS  = BNstats
module TP  = TpNull.Prover
module Co  = Constants
module H   = Hashtbl
module PH  = A.Predicate.Hash

open Misc.Ops

let mydebug = false 

let tag_of_qual = snd <.> Q.pred_of_t

module V : Graph.Sig.COMPARABLE with type t = Q.t = struct
  type t = Q.t
  let hash    = tag_of_qual <+> H.hash
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

module TTM = Map.Make (struct
    type t = A.tag * A.tag 
    let compare = compare 
  end)

(* type def  = Ast.pred * (Ast.Qualifier.t * Ast.Subst.t) *)

type p    = Sy.t * Q.def

type bind = Q.def list list

type t   = 
  { tpc : TP.t
  ; m    : bind SM.t
  ; assm : FixConstraint.soln (* invariant assumption for K, should be a fixpoint wrt constraints *)
  ; qm   : (Q.t * int) SSM.t  (* name :-> (qualif, rank) *)
  ; impm : bool TTM.t         (* (t1,t2) \in impm iff q1 => q2 /\ t1 = tag_of_qual q1 /\ t2 = tag_of_qual q2 *)
  ; impg : G.t                (* same as impm but in graph format *) 
  ; imp_memo_t: ((A.tag * A.tag), bool) H.t

  (* stats *)
  ; stat_simple_refines : int ref 
  ; stat_tp_refines     : int ref 
  ; stat_imp_queries    : int ref 
  ; stat_valid_queries  : int ref 
  ; stat_matches        : int ref 
  ; stat_umatches       : int ref 
  ; stat_unsatLHS       : int ref 
  ; stat_emptyRHS       : int ref 
}

let pprint_ps =
  Misc.pprint_many false ";" P.print 

let print_dep ppf ((_, (p, (q, su))),_) = 
  F.fprintf ppf "(%a, %s%a)" P.print p (Q.name_of_t q) Su.print su

let pprint_ds = 
  Misc.pprint_many false ";" print_dep

let pprint_qs ppf = 
  F.fprintf ppf "[%a]" (Misc.pprint_many false ";" Q.print)

let pprint_qs' ppf = 
  List.map (fst <+> snd <+> snd <+> fst) <+> pprint_qs ppf 

(*************************************************************)
(************* Constructing Initial Solution *****************)
(*************************************************************)


let def_of_pred_qual (p, q) =
  let qp = Q.pred_of_t q in
  match A.unify_pred qp p with
  | Some su -> (p, q, su)
  | None    -> assertf "ERROR: unify q=%s p=%s" (P.to_string qp) (P.to_string p)

(* HEIRARCHICAL SOL 
let map_of_bindings bs =
  List.fold_left (fun s (k, ds) -> SM.add k (List.map (fun x -> [x]) ds) s) SM.empty bs 
*)

(* {{{ CODE for NON-HEIRARCHICAL SOLUTION MAP 
let minimize s = 
  Misc.cov_filter (fun x y -> p_imp s (fst x) (fst y)) (fun _ -> true)
  <+> List.map fst

let minimize s = !Constants.minquals <?> minimize s

let minimize s qs = 
  minimize s qs
  >> F.printf "MINIMIZE: qs = [%a] qs' = [%a] \n\n" pprint_qs' qs pprint_qs'  

(* API *)
let read s k = 
  p_read s k 
  |> minimize s  
  |> List.map snd

  (* INV: qs' \subseteq qs *)
let update m k ds' =
  let ds  = SM.find k m in
  (if mydebug then 
     ds |> List.filter (fun d -> not (List.mem d ds'))
        |> List.map fst
        |> F.printf "Dropping %a: (%d) %a \n" Sy.print k
        (List.length ds) pprint_ps
  );
  (not (Misc.same_length ds ds'), SM.add k ds' m)

                              
(* API *)
let p_update s0 ks kds = 
  let kdsm = Misc.kgroupby fst kds |> Sy.sm_of_list in
  List.fold_left begin fun (b, m) k ->
    (try SM.find k kdsm with Not_found -> [])
    |> List.map snd 
    |> update m k 
    |> Misc.app_fst ((||) b)
  end (false, s0.m) ks
  |> Misc.app_snd (fun m -> { s0 with m = m })  

}}} *)

let map_of_bindings bs =
  List.fold_left begin fun s (k, ds) -> 
    ds |> List.map Misc.single 
       |> Misc.flip (SM.add k) s
  end SM.empty bs 

let quals_of_bindings bm =
  bm |> SM.range 
     |> Misc.flatten 
     |> Misc.flatten
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
     >> (List.map (fst <+> fst) <+> F.printf "CHECK_TP: %a IN %a \n" Q.print q pprint_qs)
     |> TP.set_filter tp sm vv lps (fun _ _ -> false) 
     >> (List.flatten <+> List.map fst <+> F.printf "CHECK_TP: %a OUT %a \n" Q.print q pprint_qs)

let cluster_quals = Misc.groupby Q.sort_of_t 

let update_impm_for_quals tp sm impmg qs = 
  List.fold_left begin fun impmg q ->
    let tag = tag_of_qual q in 
    qs |> check_tp tp sm q
       |> List.flatten
       |> (fun xs -> (q, tag) :: xs)
       |> List.fold_left begin fun (ttm, g) (q', tag') -> 
           ( TTM.add (tag, tag') true ttm
           , G.add_edge_e g (q, (), q'))
          end impmg
  end impmg qs

let close_env =
  List.fold_left (fun sm x -> if SM.mem x sm then sm else SM.add x Ast.Sort.t_int sm)

let impm_of_quals ts sm ps qs =
  let sm = qs |> Misc.flap (Q.pred_of_t <+> P.support) |> close_env sm in
  let tp = TP.create ts sm ps [] in
  qs |> cluster_quals 
     |> List.fold_left (update_impm_for_quals tp sm) (TTM.empty, G.empty)
     >> (fun _ -> ignore <| Printf.printf "DONE: Building IMP Graph \n")  


let qual_ranks_of_impg impg = 
  let a = SCC.scc_array impg in
  Misc.array_fold_lefti begin fun i qm qs ->
    List.fold_left begin fun qm q ->
      SSM.add (Q.name_of_t q) (q, i) qm
    end qm qs
  end SSM.empty a 

(*
let rank_of_qual s = 
  Q.name_of_t
  <+> Misc.do_catchf "rank_of_qual" (Misc.flip SSM.find s.qm)
  <+> snd
*)

let rank_of_qual s q =
  let n = Q.name_of_t q in
  let _ = asserti (SSM.mem n s.qm) "rank_of_qual crashes on: %s" (Misc.fsprintf Q.print q) in 
  snd (SSM.find n s.qm)


let p_read s k =
  let _ = asserts (SM.mem k s.m) "ERROR: p_read : unknown kvar %s\n" (Sy.to_string k) in
  SM.find k s.m 
  |> List.flatten
  |> List.map (fun d -> ((k,d), fst d))
  |> (!Constants.minquals <?> Misc.fsort (fun ((_,(_,(q,_))),_) -> rank_of_qual s q))
  |> List.rev

let q_read s k =
  let _ = asserts (SM.mem k s.m) "ERROR: q_read : unknown kvar %s\n" (Sy.to_string k) in
  SM.find k s.m 
  |> List.map List.hd
  |> List.map fst

let p_imp_subst su1 su2 = 
  Misc.join fst (Su.to_list su1) (Su.to_list su2)
  |> List.for_all (fun ((_,e1), (_, e2)) -> e1 = e2)

let p_imp_qual s q1 q2 =
  TTM.mem (Misc.map_pair tag_of_qual (q1, q2)) s.impm 

(* API *)
let p_imp s (_, (p1, (q1, su1)))  (_, (p2, (q2, su2))) =
  Misc.do_memo s.imp_memo_t begin fun ((q1,su1), (q2,su2)) ->
    p_imp_subst su1 su2 && p_imp_qual s q1 q2
  end ((q1, su1), (q2, su2)) (snd p1, snd p2)
(*  >> F.printf "P_IMP: [p1 = %a] [p2 = %a] [res = %b]\n" P.print p1 P.print p2
*)
    
(* {{{ CODE for NON-HEIRARCHICAL SOLUTION MAP 
  (* INV: qs' \subseteq qs *)
let update m k ds' =
  let ds  = SM.find k m in
  (if mydebug then 
     ds |> List.filter (fun d -> not (List.mem d ds'))
        |> List.map fst
        |> F.printf "Dropping %a: (%d) %a \n" Sy.print k
        (List.length ds) pprint_ps
  );
  (not (Misc.same_length ds ds'), SM.add k ds' m)

                              
(* API *)
let p_update s0 ks kds = 
  let kdsm = Misc.kgroupby fst kds |> Sy.sm_of_list in
  List.fold_left begin fun (b, m) k ->
    (try SM.find k kdsm with Not_found -> [])
    |> List.map snd 
    |> update m k 
    |> Misc.app_fst ((||) b)
  end (false, s0.m) ks
  |> Misc.app_snd (fun m -> { s0 with m = m })  

}}} *)


(*  CODE for HEIRARCHICAL SOLUTION MAP *)

(* INV: qs' \subseteq qs *)
let update m k dss' =
  let dss = SM.find k m in
  (not (Misc.same_length dss dss'), SM.add k dss' m)

let reprs kds = match kds with
  | (k,d)::kds' -> 
      if List.for_all (fst <+> (=) k) kds' 
      then [kds]
      else List.map Misc.single kds

(* API *)
let p_update s0 ks kdss =
  let kdsm = kdss |> Misc.flap reprs 
                  |> Misc.kgroupby (List.hd <+> fst) 
                  |> SM.of_list in
  List.fold_left begin fun (b, m) k ->
    (try SM.find k kdsm with Not_found -> [])
    |> List.map (List.map snd) 
    |> update m k 
    |> Misc.app_fst ((||) b)
  end (false, s0.m) ks
  |> Misc.app_snd (fun m -> { s0 with m = m })  

(* API *)
let top s ks = snd <| p_update s ks [] 

(************************************************************)
(*********************** Profile/Stats **********************)
(************************************************************)

let minimize s = 
  Misc.cov_filter (fun x y -> p_imp s (fst x) (fst y)) (fun _ -> true)
  <+> List.map fst

let minimize s qs = 
  minimize s qs
  >> F.printf "MINIMIZE: qs = [%a] qs' = [%a] \n\n" pprint_qs' qs pprint_qs'  

let print_m ppf s = 
  SM.to_list s.m 
  |> List.map fst 
  >> List.iter begin fun k ->
       q_read s k
       |> F.fprintf ppf "//solution: %a := [%a] \n\n"  Sy.print k pprint_ps
     end 
  >> List.iter begin fun k ->
       p_read s k
       |> F.fprintf ppf "solution: %a := [%a] \n\n"  Sy.print k pprint_ds
     end
  |> ignore
 
let print_qm ppf s = 
  SSM.to_list s.qm
  |> List.map (snd <+> fst)
  >> (fun _ -> F.fprintf ppf "//QUALIFIERS \n\n")
  |> List.iter (F.fprintf ppf "%a@ \n" Q.print) 
  |> ignore

(* API *)
let print ppf s = s >> print_m ppf >> print_qm ppf |> ignore

      
(* API *)
let print_stats ppf me =
  let (sum, max, min, bot) =   
    (SM.fold (fun _ qs x -> (+) x (List.length qs)) me.m 0,
     SM.fold (fun _ qs x -> max x (List.length qs)) me.m min_int,
     SM.fold (fun _ qs x -> min x (List.length qs)) me.m max_int,
     SM.fold (fun _ qs x -> x + (if List.exists (fst <+> P.is_contra)
     (List.flatten qs) then 1 else 0)) me.m 0) in
  let n   = SM.length me.m in
  let avg = (float_of_int sum) /. (float_of_int n) in
  F.fprintf ppf "# Vars: (Total=%d, False=%d) Quals: (Total=%d, Avg=%f, Max=%d, Min=%d)\n" 
    n bot sum avg max min;
  F.fprintf ppf "#Iteration Profile = (si=%d tp=%d unsatLHS=%d emptyRHS=%d) \n"
    !(me.stat_simple_refines) !(me.stat_tp_refines)
    !(me.stat_unsatLHS) !(me.stat_emptyRHS);
  F.fprintf ppf "#Queries: umatch=%d, match=%d, ask=%d, valid=%d\n" 
    !(me.stat_umatches) !(me.stat_matches) !(me.stat_imp_queries)
    !(me.stat_valid_queries);
  F.fprintf ppf "%a" TP.print_stats me.tpc

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
let mkbind = id

(* API *)
let dump s = 
  s.m 
  |> SM.to_list 
  |> List.map (snd <+> List.flatten <+> List.map fst)
  |> Misc.groupby key_of_quals
  |> List.map begin function 
     | [] -> assertf "impossible" 
     | (ps::_ as pss) -> Co.cprintf Co.ol_solve 
                         "SolnCluster: preds %d = size %d \n"
                         (List.length ps) (List.length pss)
     end
  |> ignore

(***************************************************************)
(************************** Refinement *************************)
(***************************************************************)

let rhs_cands s = function
  | C.Kvar (su, k) -> 
      k |> p_read s 
        |> List.map (fun (x, q) -> (x, A.substs_pred q su))
  | _ -> []

let check_tp me env vv t lps f =  function [] -> [] | rcs ->
  let env = SM.map snd3 env |> SM.add vv t in
  let rv  = TP.set_filter me.tpc env vv lps f rcs in
  let _   = ignore(me.stat_tp_refines    += 1);
            ignore(me.stat_imp_queries   += (List.length rcs));
            ignore(me.stat_valid_queries += (List.length rv)) in
  rv


(* API *)
(*
 let read s = {
    C.read  = q_read s
  ; C.bindm = s.m 
} 
*)

(* API *)
let read s k = (s.assm k) ++ (if SM.mem k s.m    then q_read s k else [])

(* API *)
let read_bind s k = failwith "TBD"

(* API *)
let refine me c =
  let env = C.env_of_t c in
  let (vv1, t1, _) = C.lhs_of_t c in
  let (_,_,ra2s) as r2 = C.rhs_of_t c in
  let k2s = r2 |> C.kvars_of_reft |> List.map snd in
  let rcs = BS.time "rhs_cands" (Misc.flap (rhs_cands me)) ra2s in
  if rcs = [] then
    let _ = me.stat_emptyRHS += 1 in
    (false, me)
  else 
    let lps = BS.time "preds_of_lhs" (C.preds_of_lhs (read me)) c in
    if BS.time "lhs_contra" (List.exists P.is_contra) lps then 
    let _ = me.stat_unsatLHS += 1 in
    let _ = me.stat_umatches += List.length rcs in
    (false, me)
  else
    let rcs     = List.filter (fun (_,p) -> not (P.is_contra p)) rcs in
    let lt      = PH.create 17 in
    let _       = List.iter (fun p -> PH.add lt p ()) lps in
    let (x1,x2) = List.partition (fun (_,p) -> PH.mem lt p) rcs in
    let _       = me.stat_matches += (List.length x1) in
    let kqs1    = List.map fst x1 |> List.map Misc.single in
    (if C.is_simple c 
     then (ignore(me.stat_simple_refines += 1); kqs1) 
     else kqs1 ++ (BS.time "check tp" (check_tp me env vv1 t1 lps (p_imp me)) x2))
    |> p_update me k2s 

(***************************************************************)
(************************* Satisfaction ************************)
(***************************************************************)

let unsat me c = 
  let env      = C.env_of_t c in
  let (vv,t,_) = C.lhs_of_t c in
  let s        = read me      in
  let lps      = C.preds_of_lhs s c  in
  let rhsp     = c |> C.rhs_of_t |> C.preds_of_reft s |> A.pAnd in
  let f        = fun _ _ -> false in
  not ((check_tp me env vv t lps f [(0, rhsp)]) = [[0]])

(*
let unsat me c = 
  let msg = Printf.sprintf "unsat_cstr %d" (C.id_of_t c) in
  Misc.do_catch msg (unsat me s) c
*)

(***************************************************************)
(******************** Qualifier Instantiation ******************)
(***************************************************************)

let wellformed env q = 
  A.sortcheck_pred (fun x -> snd3 (SM.find x env)) (Q.pred_of_t q)
(*  >> (F.printf "\nwellformed: q = @[%a@] in env = @[%a@] result %b\n"  
        Q.print q (C.print_env None) env)
 *)

let dupfree_binding xys : bool = 
  let ys  = List.map snd xys in
  let ys' = Misc.sort_and_compact ys in
  List.length ys = List.length ys'

let varmatch_ctr = ref 0

let varmatch (x, y) = 
  let _ = varmatch_ctr += 1 in
  let (x,y) = Misc.map_pair Sy.to_string (x,y) in
  if x.[0] = '@' then
    let x' = Misc.suffix_of_string x 1 in
    Misc.is_prefix x' y
  else true

let valid_binding xys = 
  (dupfree_binding xys) && (List.for_all varmatch xys)

let valid_bindings ys x = 
  ys |> List.map (fun y -> (x, y))
     |> List.filter varmatch 

let inst_qual ys t' (q : Q.t) : (Q.t * (Q.t * Su.t)) list =
  let v  = Q.vv_of_t   q in
  let p  = Q.pred_of_t q in
  let q' = Q.create "" v t' p in
  let v' = Sy.value_variable t' in
  let su = Su.of_list [(v, A.eVar v')] in 
  begin
  match q' |> Q.pred_of_t |> P.support |> List.filter Sy.is_wild with
  | [] -> 
      [q', (q, su)]
  | xs -> 
      xs
      |> Misc.sort_and_compact
      |> List.map (valid_bindings ys)                   (* candidate bindings    *)
      |> Misc.product                                   (* generate combinations *) 
      |> List.filter valid_binding                      (* remove bogus bindings *)
      |> List.map (List.map (Misc.app_snd A.eVar))      (* instantiations        *)
      |> List.rev_map Su.of_list                        (* convert to substs     *)
      |> List.rev_map (fun su' -> (Q.subst su' q', (q, Su.concat su su'))) (* quals *)
  end
(*  >> ((List.map fst) <+> F.printf "\n\ninst_qual q = %a: %a" Q.print q (Misc.pprint_many true "" Q.print))
 *)

let inst_ext qs wf = 
  let r    = C.reft_of_wf wf in
  let ks   = C.kvars_of_reft r |> List.map snd in
  let env  = C.env_of_wf wf in
  let ys   = SM.fold (fun y _ ys -> y::ys) env [] in
  let vv   = fst3 r in
  let t    = snd3 r in
  let env' = SM.add vv r env in
  qs |> List.filter (fun q -> not (A.Sort.unify [t] [Q.sort_of_t q] = None))
     |> Misc.flap   (inst_qual ys t)
     |> Misc.map    (Misc.app_fst (Q.subst_vv vv))
     |> Misc.filter (fst <+> wellformed env')
     |> Misc.filter (fst <+> C.filter_of_wf wf)
     |> Misc.map    (Misc.app_fst Q.pred_of_t)
     |> Misc.cross_product ks

let inst ws qs = 
  Misc.flap (inst_ext qs) ws 
  >> (fun _ -> Co.bprintf mydebug "\n\nvarmatch_ctr = %d \n\n" !varmatch_ctr)
  |> Misc.kgroupby fst 
  |> Misc.map (Misc.app_snd (List.map snd)) 

(*************************************************************************)
(*************************** Creation ************************************)
(*************************************************************************)

(* API *)
let create ts sm ps consts assm bm =
  (* let m          = map_of_bindings bs in *)
  let qs         = quals_of_bindings bm in
  let im, ig, qm =
    if !Constants.minquals then
      impm_of_quals ts sm ps qs
      >> (snd <+> dump_graph (!Constants.save_file^".impg.dot")) 
      |> (fun (im, ig) -> (im, ig, qual_ranks_of_impg ig)) 
    else
      (TTM.empty, G.empty, List.map (fun q -> (Q.name_of_t q, (q, 0))) qs |> SSM.of_list) 
  in { m = bm; assm = assm; qm = qm
     ; impm = im; impg = ig; imp_memo_t = H.create 37
     ; tpc  = TP.create ts sm ps (List.map fst consts)
     ; stat_simple_refines = ref 0
     ; stat_tp_refines     = ref 0; stat_imp_queries    = ref 0
     ; stat_valid_queries  = ref 0; stat_matches        = ref 0
     ; stat_umatches       = ref 0; stat_unsatLHS       = ref 0
     ; stat_emptyRHS       = ref 0
     }

let ppBinding (k, zs) = 
  F.printf "ppBind %a := %a \n" 
    Sy.print k 
    (Misc.pprint_many false "," P.print) (List.map fst zs)

(* Take in a solution of things that are known to be true, kf. Using
   this, we can prune qualifiers whose negations are implied by
   information in kf *)
let update_pruned ks me fqm =
  List.fold_left begin fun m k ->
    if SM.mem k fqm then
      let false_qs = SM.find k fqm |> Misc.flatten  in
      let qs = SM.find k m
             |> List.map (List.filter (fun q -> (not (List.mem (k,q) false_qs))))
	     |> List.filter (fun q -> q <> [])
      in
	SM.add k qs m
    else
      m
  end
    me.m
    ks


let apply_facts_c kf me c =
  let env = C.env_of_t c in
  let (vv, t, lras) as lhs = C.lhs_of_t c in
  let (_,_,ras) as rhs = C.rhs_of_t c in
  let ks = rhs |> C.kvars_of_reft |> List.map snd in
  let lps = C.preds_of_lhs kf c in (* Use the known facts here *)
  let rcs = (Misc.flap (rhs_cands me)) ras in
  let f _ _ = false in
    if rcs = [] then
      (* Nothing on the right hand side *)
      me
(*    else if List.exists P.is_contra lps then
      me *)
    else if check_tp me env vv t lps f [(0, A.pFalse)] = [[0]] then
      me
    else
      
      let rcs = List.filter (fun (_,p) -> not (P.is_contra p)) rcs
                |> List.map (fun (x,p) -> (x, A.pNot p)) in
	(* can we prove anything on the left implies something on the
	   right is false? *)
      let fqs = BS.time "apply_facts tp" (check_tp me env vv t lps f) rcs in
      let fqm = fqs |> Misc.flap reprs 
                    |> Misc.kgroupby (List.hd <+> fst)
                    |> SM.of_list
      in
	{me with m = BS.time "update pruned" (update_pruned ks me) fqm}

let apply_facts kf me cs =
  let numqs = me.m |> Ast.Symbol.SMap.to_list
              |> List.map snd |> List.concat |> List.length in
  let sol   = List.fold_left (apply_facts_c kf) me cs in
  let numqs' = sol.m |> Ast.Symbol.SMap.to_list
               |> List.map snd |> List.concat |> List.length in
  let _ = Printf.printf "Started with %d, proved %d false\n" numqs (numqs-numqs') in
    sol

(* API *)
let create c facts = 
  c.Config.qs 
  |> Q.normalize 
  >> Co.logPrintf "Using Quals: \n%a" (Misc.pprint_many true "\n" Q.print) 
  |> BS.time "Qual Inst" (inst c.Config.ws) (* >> List.iter ppBinding *)
  |> map_of_bindings
  |> SM.extendWith (fun _ -> (++)) c.Config.bm
  |> create c.Config.ts c.Config.uops c.Config.ps c.Config.cons c.Config.assm
  |> fun me -> match facts with
       | None -> me
       | Some kf -> BS.time "apply facts" (apply_facts kf me) (c.Config.cs)
	     

(* API *)
let empty = create Config.empty None

(* API *)
let meet me you = {me with m = SM.extendWith (fun _ -> (++)) me.m you.m} 

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
