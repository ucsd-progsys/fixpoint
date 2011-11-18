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
module Cg  = FixConfig
module H   = Hashtbl
module PH  = A.Predicate.Hash

open Misc.Ops


let mydebug = false 

let tag_of_qual  = snd <.> Q.pred_of_t
let tag_of_qual2 = Misc.map_pair tag_of_qual

module QS = Misc.ESet (struct
  type t = Q.t
  let compare x y = compare (tag_of_qual x) (tag_of_qual y)
end)

module Q2S = Misc.ESet (struct
  type t = Q.t * Q.t
  let compare x y = compare (tag_of_qual2 x) (tag_of_qual2 y)
end)


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

module TTM = Misc.EMap (struct
    type t = A.tag * A.tag 
    let compare = compare 
  end)

type bind = Q.def list

type t   = 
  { tpc  : TP.t
  ; m    : bind SM.t
  ; assm : FixConstraint.soln (* invariant assumption for K, 
                                 must be a fixpoint wrt constraints *)
  ; qs   : QS.t 
  ; qleqs: Q2S.t              (* (q1,q2) \in qleqs implies q1 => q2 *)
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

let print_dep ppf (p, (q, su)) = 
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

(*
let map_of_bindings bs =
  List.fold_left begin fun s (k, ds) -> 
    ds |> List.map Misc.single 
       |> Misc.flip (SM.add k) s
  end SM.empty bs 
*)

let quals_of_bindings bm =
  bm |> SM.range 
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

(* {{{
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

 }}} *)

let p_read s k =
  let _ = asserts (SM.mem k s.m) "ERROR: p_read : unknown kvar %s\n" (Sy.to_string k) in
  SM.find k s.m  |>: (fun d -> ((k, d), fst d))

(* INV: qs' \subseteq qs *)
let update m k ds' =
  let ds = try SM.find k m with Not_found -> [] in
  (not (Misc.same_length ds ds'), SM.add k ds' m)

let p_update s0 ks kds = 
  let kdsm = Misc.kgroupby fst kds |> SM.of_list in
  List.fold_left begin fun (b, m) k ->
    (try SM.find k kdsm with Not_found -> [])
    |> List.map snd 
    |> update m k 
    |> Misc.app_fst ((||) b)
  end (false, s0.m) ks
  |> Misc.app_snd (fun m -> { s0 with m = m })  

(* API *)
let top s ks = 
  ks (* |> List.partition (fun k -> SM.mem k s.m)
     >> (fun (_, badks) -> Co.logPrintf "WARNING: Trueing Unbound KVars = %s \n" (Misc.fsprintf (Misc.pprint_many false "," Sy.print) badks))
     |> fst *)
     |> Misc.flip (p_update s) []
     |> snd



(************************************************************)
(*********************** Profile/Stats **********************)
(************************************************************)

let print_m ppf s = 
  SM.to_list s.m 
  |> List.iter begin fun (k, ds) ->
       ds >>  F.fprintf ppf "solution: %a := [%a] \n\n"  Sy.print k pprint_ds
          |>: fst
   (* >>  F.fprintf ppf "//solution: %a := [%a] \n\n"  Sy.print k pprint_ps *)
          |> ignore
     end 
 
let print_qs ppf s = 
  QS.elements s.qs
  >> (fun _ -> F.fprintf ppf "//QUALIFIERS \n\n")
  |> F.fprintf ppf "%a" (Misc.pprint_many true "\n" Q.print)
(*  |> List.iter (F.fprintf ppf "%a" Q.print) 
 *) |> ignore

(* API *)
let print ppf s = s >> print_m ppf >> print_qs ppf |> ignore

     
let botInt qs = if List.exists (fst <+> P.is_contra) qs then 1 else 0

(* API *)
let print_stats ppf me =
  let (sum, max, min, bot) =   
    (SM.fold (fun _ qs x -> (+) x (List.length qs)) me.m 0,
     SM.fold (fun _ qs x -> max x (List.length qs)) me.m min_int,
     SM.fold (fun _ qs x -> min x (List.length qs)) me.m max_int,
     SM.fold (fun _ qs x -> x + botInt qs) me.m 0) in
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
let mkbind = Misc.flatten <+> Misc.sort_and_compact

(* API *)
let dump s = 
  s.m 
  |> SM.to_list 
  |> List.map (snd <+> List.map fst)
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
  | C.Kvar (su, k) -> k |> p_read s |>: (Misc.app_snd (Misc.flip A.substs_pred su))
  | _ -> []

let check_tp me env vv t lps =  function [] -> [] | rcs ->
  let env = SM.map snd3 env |> SM.add vv t in
  let rv  = TP.set_filter me.tpc env vv lps (fun _ _ -> false) rcs |>: List.hd in
  let _   = ignore(me.stat_tp_refines    += 1);
            ignore(me.stat_imp_queries   += (List.length rcs));
            ignore(me.stat_valid_queries += (List.length rv)) in
  rv


(* API *)
let read s k = (s.assm k) ++ (if SM.mem k s.m then p_read s k |>: snd else [])

(* API *)
let read_bind s k = failwith "TBD: read_bind"


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
    let kqs1    = List.map fst x1 in
    (if C.is_simple c 
     then (ignore(me.stat_simple_refines += 1); kqs1) 
     else kqs1 ++ (BS.time "check tp" (check_tp me env vv1 t1 lps) x2))
    |> p_update me k2s 


(***************************************************************)
(****************** Sort Check Based Refinement ****************)
(***************************************************************)

(* API *)
let wellformed_pred env p =
  Misc.do_catch_ret "PA.wellformed: sortcheck_pred " 
    (A.sortcheck_pred (fun x -> snd3 (SM.find x env))) 
    p 
    false

let refts_of_c c =
  [ C.lhs_of_t c ; C.rhs_of_t c] ++ (C.env_of_t c |> C.bindings_of_env |>: snd)

let refine_sort_reft env me ((vv, so, ras) as r) = 
  let env' = SM.add vv r env in 
  let ks   = r |> C.kvars_of_reft |>: snd in
  ras |> Misc.flap (rhs_cands me)
      |> List.filter (fun (_,p) -> wellformed_pred env' p)
      |> List.map fst
      |> p_update me ks
      |> snd

(* API *)
let refine_sort me c =
  let env = C.env_of_t c in
  c |> refts_of_c 
    |> List.fold_left (refine_sort_reft env) me  

(***************************************************************)
(************************* Satisfaction ************************)
(***************************************************************)

let unsat me c = 
  let env      = C.env_of_t c in
  let (vv,t,_) = C.lhs_of_t c in
  let s        = read me      in
  let lps      = C.preds_of_lhs s c  in
  let rhsp     = c |> C.rhs_of_t |> C.preds_of_reft s |> A.pAnd in
  not ((check_tp me env vv t lps [(0, rhsp)]) = [0])

(*
let unsat me c = 
  let msg = Printf.sprintf "unsat_cstr %d" (C.id_of_t c) in
  Misc.do_catch msg (unsat me s) c
*)

(****************************************************************)
(************* Minimization: For Prettier Output ****************)
(****************************************************************)

let canonize_subs = 
  Su.to_list <+> List.sort (fun (x,_) (y,_) -> compare x y)

let subst_leq =
  Misc.map_pair canonize_subs <+> Misc.isPrefix
 
let qual_leq s = 
  Misc.flip Q2S.mem s.qleqs

let def_leq s (_, (q1, su1)) (_, (q2, su2)) = 
  qual_leq s (q1, q2) && subst_leq (su1, su2)

let min_read s k = 
  if SM.mem k s.m then 
    SM.find k s.m 
    |> Misc.rootsBy (def_leq s)  
    |> List.map fst 
  else []

(* API *)
let min_read s k =
  if !Constants.minquals then min_read s k else read s k

(*  check_leq tp sm q qs = [q' | q' <- qs, Z3 |- q => q'] *)
let check_leq tp sm (q : Q.t) (qs : Q.t list) : Q.t list = 
  let vv  = Q.vv_of_t q in
  let lps = [Q.pred_of_t q] in
  qs |> List.map (fun q -> (q, Q.pred_of_t q))
     >> (List.map fst <+> F.printf "CHECK_TP: %a IN %a \n" Q.print q pprint_qs)
     |> TP.set_filter tp sm vv lps (fun _ _ -> false)
     |> List.flatten
     >> F.printf "CHECK_TP: %a OUT %a \n" Q.print q pprint_qs

let qimps_of_partition tp sm qs =
  foreach qs begin fun q ->
    let qs' = check_leq tp sm q qs in
    foreach qs' begin fun q' ->
      (q, q')
    end
  end

let close_env qs sm =
  qs |> Misc.flap   (Q.pred_of_t <+> P.support) 
     |> Misc.filter (not <.> Misc.flip SM.mem sm)
     |> Misc.map    (fun x -> (x, Ast.Sort.t_int))
     |> SM.of_list
     |> SM.extend sm

let qleqs_of_qs ts sm ps qs =
  let sm = close_env qs sm       in
  let tp = TP.create ts sm ps [] in
  qs |> Misc.groupby Q.sort_of_t
     |> Misc.flap (qimps_of_partition tp sm)
     |> Misc.flatten
     |> Q2S.of_list
     >> (fun _ -> ignore <| Printf.printf "DONE: Building qleqs_of_qs \n")  

(***************************************************************)
(******************** Qualifier Instantiation ******************)
(***************************************************************)


let wellformed_qual env q =
  wellformed_pred env (Q.pred_of_t q)
  
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
  List.for_all varmatch xys

let valid_bindings ys x =
  ys |> List.map (fun y -> (x, y))
     |> List.filter varmatch

let sort_compat t1 t2 = A.Sort.unify [t1] [t2] <> None

let valid_bindings_sort env (x, t) =
  env |> SM.to_list
      |> Misc.filter (snd <+> C.sort_of_reft <+> (sort_compat t))
      |> Misc.map (fun (y,_) -> (x, y))
      |> Misc.filter varmatch

let valid_bindings env ys (x, t) =
  if !Constants.sorted_quals
  then valid_bindings_sort env (x,t)
  else valid_bindings ys x

let inst_qual env ys t' (q : Q.t) : (Q.t * (Q.t * Su.t)) list =
  let v  = Q.vv_of_t   q in
  let p  = Q.pred_of_t q in
  let q' = Q.create "" v t' (Q.params_of_t q) p in
  let v' = Sy.value_variable t' in
  let su = Su.of_list [(v, A.eVar v')] in
  begin
  (*match q' |> Q.pred_of_t |> P.support |> List.filter Sy.is_wild with
  | [] ->
      [q', (q, su)]
  | xs ->
      xs *)
  match q' |> Q.params_of_t |> Sy.SMap.to_list with
  | [] ->
      [q', (q, su)]
  | xts ->
      xts
      |> Misc.sort_and_compact
      |> List.map (valid_bindings env ys)               (* candidate bindings    *)
      |> Misc.product                                   (* generate combinations *) 
      |> List.filter valid_binding                      (* remove bogus bindings *)
      |> List.map (List.map (Misc.app_snd A.eVar))      (* instantiations        *)
      |> List.rev_map Su.of_list                        (* convert to substs     *)
      |> List.rev_map (fun su' -> (Q.subst su' q', (q, Su.concat su su'))) (* quals *)
  end
(*  >> ((List.map fst) <+> F.printf "\n\ninst_qual q = %a: %a" Q.print q (Misc.pprint_many true "" Q.print))
 *)

let inst_ext qs wf = 
  let r    = wf >> (C.id_of_wf <+>  Printf.sprintf "\nPredAbs.inst_ext wf id = %d\n" <+> print_now)
                |> C.reft_of_wf in
  let ks   = C.kvars_of_reft r |> List.map snd in
  let env  = C.env_of_wf wf in
  let vv   = fst3 r in
  let t    = snd3 r in
  let ys   = Sy.SMap.domain env in
  let env' = SM.add vv r env in
  qs |> List.filter (Q.sort_of_t <+> sort_compat t)
     |> Misc.flap   (inst_qual env ys t)
     |> Misc.map    (Misc.app_fst (Q.subst_vv vv))
     |> Misc.filter (fst <+> wellformed_qual env')
     |> Misc.filter (fst <+> C.filter_of_wf wf)
     |> Misc.map    (Misc.app_fst Q.pred_of_t)
     |> Misc.cross_product ks

(*
let flapn s f = 
  let rec go acc n = function
    | []    -> acc
    | x::xs -> (print_now (Printf.sprintf "flap %s %d" s n); 
                go ((f x) ++ acc) (n+1) xs)
  in go [] 0 
*)

let inst ws qs = 
  Misc.flap (inst_ext qs) ws 
  >> (fun _ -> Co.bprintf mydebug "\n\nvarmatch_ctr = %d \n\n" !varmatch_ctr)
  |> Misc.kgroupby fst 
  |> Misc.map (Misc.app_snd (List.map snd)) 

(*************************************************************************)
(*************************** Creation ************************************)
(*************************************************************************)

let create ts sm ps consts assm qs0 bm =
  let qs         = Misc.sort_and_compact (qs0 ++ quals_of_bindings bm) in
  { m = bm; assm = assm; qs = QS.of_list qs
  ; qleqs               = if !Constants.minquals then qleqs_of_qs ts sm ps qs else Q2S.empty
  ; tpc                 = TP.create ts sm ps (List.map fst consts)
  ; stat_simple_refines = ref 0
  ; stat_tp_refines     = ref 0; stat_imp_queries    = ref 0
  ; stat_valid_queries  = ref 0; stat_matches        = ref 0
  ; stat_umatches       = ref 0; stat_unsatLHS       = ref 0
  ; stat_emptyRHS       = ref 0
  }

(* RJ: DO NOT DELETE! *)
let ppBinding (k, zs) = 
  F.printf "ppBind %a := %a \n" 
    Sy.print k 
    (Misc.pprint_many false "," P.print) (List.map fst zs)

(* Take in a solution of things that are known to be true, kf. Using
   this, we can prune qualifiers whose negations are implied by
   information in kf *)
let update_pruned ks me fqm =
  List.fold_left begin fun m k ->
    if not (SM.mem k fqm) then m else
      let false_qs = SM.find k fqm in
      let qs = SM.find k m 
               |> List.filter (fun q -> (not (List.mem (k,q) false_qs))) 
      in SM.add k qs m
  end me.m ks

let apply_facts_c kf me c =
  let env = C.env_of_t c in
  let (vv, t, lras) = C.lhs_of_t c in
  let (_,_,ras) as rhs = C.rhs_of_t c in
  let ks = rhs |> C.kvars_of_reft |> List.map snd in
  let lps = C.preds_of_lhs kf c in (* Use the known facts here *)
  let rcs = (Misc.flap (rhs_cands me)) ras in
    if rcs = [] then (* Nothing on the right hand side *)
      me
    else if check_tp me env vv t lps [(0, A.pFalse)] = [0] then
      me
    else
      let rcs = List.filter (fun (_,p) -> not (P.is_contra p)) rcs
                |> List.map (fun (x,p) -> (x, A.pNot p)) in
	(* can we prove anything on the left implies something on the
	   right is false? *)
      let fqs = BS.time "apply_facts tp" (check_tp me env vv t lps) rcs in
      let fqm = fqs |> Misc.kgroupby fst |> SM.of_list in
	  {me with m = BS.time "update pruned" (update_pruned ks me) fqm}

let apply_facts cs kf me =
  let numqs = me.m |> Ast.Symbol.SMap.to_list
              |> List.map snd |> List.concat |> List.length in
  let sol   = List.fold_left (apply_facts_c kf) me cs in
  let numqs' = sol.m |> Ast.Symbol.SMap.to_list
               |> List.map snd |> List.concat |> List.length in
  let _ = Printf.printf "Started with %d, proved %d false\n" numqs (numqs-numqs') in
    sol

let binds_of_quals ws qs =
  qs
  |> Q.normalize
  >> Co.logPrintf "Using Quals: \n%a" (Misc.pprint_many true "\n" Q.print) 
  >> (fun _ -> flush stdout)
  |> BS.time "Qual Inst" (inst ws) 
  (* >> List.iter ppBinding *)
  |> SM.of_list 
  >> (fun _ -> flush stdout)

(* API *)
let create c facts = 
  SM.empty
  |> ((!Constants.dump_simp != "") <?> (fun _ -> binds_of_quals c.Cg.ws c.Cg.qs))
  |> SM.extendWith (fun _ -> (++)) c.Cg.bm
  |> create c.Cg.ts c.Cg.uops c.Cg.ps c.Cg.cons c.Cg.assm c.Cg.qs
  |> ((!Constants.refine_sort) <?> Misc.flip (List.fold_left refine_sort) c.Cg.cs)
  |> Misc.maybe_apply (apply_facts c.Cg.cs) facts

  (*
  |> fun me -> match facts with
       | None -> me
       | Some kf -> BS.time "apply facts" (apply_facts me kf) (c.Cg.cs)
*)	    



(* API *)
let empty = create Cg.empty None

(* API *)
let meet me you = {me with m = SM.extendWith (fun _ -> (++)) me.m you.m} 



