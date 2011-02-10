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


(** This module implements a fixpoint solver *)
module BS = BNstats
module F  = Format
module A  = Ast
module Co = Constants
module P  = A.Predicate
module E  = A.Expression
module So = A.Sort
module Su = A.Subst
module Q  = A.Qualifier
module PH = A.Predicate.Hash
module Sy = A.Symbol
module SM = Sy.SMap
module C  = FixConstraint
module Ci = Cindex
module TP = TpNull.Prover
module PP = Prepass

open Misc.Ops

type t = {
   tpc : TP.t
 ; sri : Ci.t
 ; ws  : C.wf list
 ; tt  : Timer.t
   
 (* Stats *)
 ; stat_refines        : int ref
 ; stat_simple_refines : int ref 
 ; stat_tp_refines     : int ref 
 ; stat_imp_queries    : int ref 
 ; stat_valid_queries  : int ref 
 ; stat_matches        : int ref 
 ; stat_umatches       : int ref 
 ; stat_unsatLHS       : int ref 
 ; stat_emptyRHS       : int ref 
 ; stat_cfreqt         : (int, int) Hashtbl.t 
}

let mydebug = true 

(*************************************************************)
(********************* Stats *********************************)
(*************************************************************)

let hashtbl_incr_frequency t k = 
  let n = try Hashtbl.find t k with Not_found -> 0 in
  Hashtbl.replace t k (n+1)

let hashtbl_print_frequency t = 
  Misc.hashtbl_to_list t 
  |> Misc.groupby snd
  |> List.map (function ((_,n)::_) as xs -> (n, List.length xs) | _ -> assertf "impossible") 
  |> List.sort compare
  |> List.iter (fun (n,m) -> Format.printf "ITERFREQ: %d times %d constraints \n" n m)


(***************************************************************)
(************************** Refinement *************************)
(***************************************************************)

let rhs_cands s = function
  | C.Kvar (su, k) -> 
      k |> FixSolution.p_read s 
        |> List.map (fun (x, q) -> (x, A.substs_pred q su))
        (* |> List.map (fun q -> ((k,q), A.substs_pred q su)) *)
  | _ -> []

let check_tp me env vv t lps f =  function [] -> [] | rcs ->
  let env = SM.map snd3 env |> SM.add vv t in
  let rv  = TP.set_filter me.tpc env vv lps f rcs in
  let _   = ignore(me.stat_tp_refines    += 1);
            ignore(me.stat_imp_queries   += (List.length rcs));
            ignore(me.stat_valid_queries += (List.length rv)) in
  rv

let refine me s c =
  let _   = me.stat_refines += 1 in
  let env = C.env_of_t c in
  let (vv1, t1, _) = C.lhs_of_t c in
  let (_,_,ra2s) as r2 = C.rhs_of_t c in
  let k2s = r2 |> C.kvars_of_reft |> List.map snd in
  let rcs = BS.time "rhs_cands" (Misc.flap (rhs_cands s)) ra2s in
  if rcs = [] then
    let _ = me.stat_emptyRHS += 1 in
    (false, s)
  else 
    let lps = BS.time "preds_of_lhs" (C.preds_of_lhs s) c in
    if BS.time "lhs_contra" (List.exists P.is_contra) lps then 
    let _ = me.stat_unsatLHS += 1 in
    let _ = me.stat_umatches += List.length rcs in
    (false, s)
  else
    let rcs     = List.filter (fun (_,p) -> not (P.is_contra p)) rcs in
    let lt      = PH.create 17 in
    let _       = List.iter (fun p -> PH.add lt p ()) lps in
    let (x1,x2) = List.partition (fun (_,p) -> PH.mem lt p) rcs in
    let _       = me.stat_matches += (List.length x1) in
    let kqs1    = List.map fst x1 in
    (if C.is_simple c 
     then (ignore(me.stat_simple_refines += 1); kqs1) 
     else kqs1 ++ (BS.time "check tp" (check_tp me env vv1 t1 lps FixSolution.p_imp) x2))
    |> FixSolution.p_update s k2s 

(***************************************************************)
(************************* Satisfaction ************************)
(***************************************************************)

let unsat me s c = 
  let env      = C.env_of_t c in
  let (vv,t,_) = C.lhs_of_t c in
  let lps      = C.preds_of_lhs s c  in
  let rhsp     = c |> C.rhs_of_t |> C.preds_of_reft s |> A.pAnd in
  let f        = fun _ _ -> false in
  not ((check_tp me env vv t lps f [(0, rhsp)]) = [0])

let unsat me s c = 
  let msg = Printf.sprintf "unsat_cstr %d" (C.id_of_t c) in
  Misc.do_catch msg (unsat me s) c

let unsat_constraints me s =
  me.sri |> Ci.to_list |> List.filter (unsat me s)


(***************************************************************)
(************************ Debugging/Stats **********************)
(***************************************************************)

let print_constr_stats ppf cs = 
  let cn   = List.length cs in
  let scn  = List.length (List.filter C.is_simple cs) in
  F.fprintf ppf "#Constraints: %d (simple = %d) \n" cn scn

let print_solver_stats ppf me = 
  print_constr_stats ppf (Ci.to_list me.sri); 
  F.fprintf ppf "#Iterations = %d (si=%d tp=%d unsatLHS=%d emptyRHS=%d) \n"
    !(me.stat_refines) !(me.stat_simple_refines) !(me.stat_tp_refines)
    !(me.stat_unsatLHS) !(me.stat_emptyRHS);
  F.fprintf ppf "#Queries: umatch=%d, match=%d, ask=%d, valid=%d\n" 
    !(me.stat_umatches) !(me.stat_matches) !(me.stat_imp_queries)
    !(me.stat_valid_queries);
  F.fprintf ppf "%a" TP.print_stats me.tpc;
  F.fprintf ppf "Iteration Frequency: \n";
  hashtbl_print_frequency me.stat_cfreqt;
  F.fprintf ppf "Iteration Periods: @[%a@] \n" Timer.print me.tt;
  F.fprintf ppf "finished solver_stats \n"

let dump me s = 
  Co.cprintf Co.ol_solve_stats "%a \n" print_solver_stats me;
  Co.cprintf Co.ol_solve_stats "%a \n" FixSolution.print_stats s;
  FixSolution.dump_cluster s

(***************************************************************)
(******************** Qualifier Instantiation ******************)
(***************************************************************)

let wellformed env q = 
  A.sortcheck_pred (fun x -> snd3 (SM.find x env)) (Q.pred_of_t q) 

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

let inst_qual ys t' (q : Q.t) : Q.t list =
  let v  = Q.vv_of_t   q in
  let p  = Q.pred_of_t q in
  let v' = Sy.value_variable t' in
  let p' = P.subst p v (A.eVar v') in
  begin
  match P.support p' |> List.filter Sy.is_wild with
  | [] -> 
      [Q.create v' t' p']
  | xs -> 
      xs
      |> Misc.sort_and_compact
      |> List.map (valid_bindings ys)                   (* candidate bindings    *)
      |> Misc.product                                   (* generate combinations *) 
      |> List.filter valid_binding                      (* remove bogus bindings *)
      |> List.map (List.map (Misc.app_snd A.eVar))      (* instantiations        *)
      |> List.rev_map (Su.of_list <+> A.substs_pred p') (* substituted preds     *)
      |> List.map (Q.create v' t' )                     (* qualifiers            *)
  end
(*  >> F.printf "inst_qual q = %a: \n%a" Q.print q (Misc.pprint_many true "" Q.print) *)

let inst_ext qs wf = 
  let r    = C.reft_of_wf wf in
  let ks   = C.kvars_of_reft r |> List.map snd in
  let env  = C.env_of_wf wf in
  let ys   = SM.fold (fun y _ ys -> y::ys) env [] in
  let env' = SM.add (fst3 r) r env in
  let t    = snd3 r in
  qs |> List.filter (fun q -> not (So.unify [t] [Q.sort_of_t q] = None))
     |> Misc.flap (inst_qual ys (snd3 r))
     |> Misc.filter (wellformed env')
     |> Misc.filter (C.filter_of_wf wf)
     |> Misc.map (Q.pred_of_t <*> some)
     |> Misc.cross_product ks

let inst ws qs =
  Misc.flap (inst_ext qs) ws 
  >> (fun _ -> Co.bprintf mydebug "varmatch_ctr = %d \n" !varmatch_ctr)
  |> Misc.kgroupby fst 
  |> Misc.map (Misc.app_snd (List.map snd)) 

(***************************************************************)
(******************** Iterative Refinement *********************)
(***************************************************************)

let log_iter_stats me s = 
  (if Co.ck_olev Co.ol_insane then F.printf "%a" FixSolution.print s);
  (if !(me.stat_refines) mod 100 = 0 then 
     let msg = Printf.sprintf "num refines=%d" !(me.stat_refines) in 
     let _   = Timer.log_event me.tt (Some msg) in
     let _   = F.printf "%s" msg in 
     let _   = F.printf "%a \n" FixSolution.print_stats s in
     ());
  ()

let rec acsolve me w s =
  let _ = log_iter_stats me s in
  match Ci.wpop me.sri w with 
  | (None,_) -> 
      let _ = Timer.log_event me.tt (Some "Finished") in 
      s 
  | (Some c, w') ->
      let (ch, s')  = BS.time "refine" (refine me s) c in
      let _ = hashtbl_incr_frequency me.stat_cfreqt (C.id_of_t c) in  
      let _ = Co.bprintf mydebug "iter=%d id=%d ch=%b %a \n" 
              !(me.stat_refines) (C.id_of_t c) ch C.print_tag (C.tag_of_t c) in
      let w'' = if ch then Ci.deps me.sri c |> Ci.wpush me.sri w' else w' in 
      acsolve me w'' s' 



(* API *)
let solve me s = 
  let _  = F.printf "Fixpoint: Validating Initial Solution \n" in
  let _  = BS.time "profile" PP.profile me.sri in
  let s  = PP.true_unconstrained s me.sri in
  let _  = Co.cprintf Co.ol_insane "%a%a" Ci.print me.sri FixSolution.print s; dump me s in
  let _  = F.printf "Fixpoint: Initialize Worklist \n" in
  let w  = BS.time "init wkl" Ci.winit me.sri in 
  let _  = F.printf "Fixpoint: Refinement Loop \n" in
  let s  = BS.time "solving"  (acsolve me w) s in
  let _  = dump me s in
  let _  = F.printf "Fixpoint: Testing Solution \n" in
  let u  = BS.time "testing solution" (unsat_constraints me) s in
  let _  = if u != [] then F.printf "Unsatisfied Constraints:\n %a" (Misc.pprint_many true "\n" (C.print_t None)) u in
  (s, u)

(* API *)
let create ts sm ps a ds cs ws bs0 qs =
  let tpc = TP.create ts sm ps in
  let bs  = BS.time "Qual Inst" (inst ws) qs in
  let s   = FixSolution.of_bindings ts sm ps (bs0 ++ bs) in
  let ws  = PP.validate_wfs ws in
  let sri = cs >> F.printf "Pre-Simplify Stats\n%a" print_constr_stats 
               |> BS.time  "Simplify" FixSimplify.simplify_ts
               >> F.printf "Post-Simplify Stats\n%a" print_constr_stats
               |> BS.time  "PP.Validation" (PP.validate a s)
               |> BS.time  "Ref Index" Ci.create ds in
  ({ tpc                 = tpc
   ; sri                 = sri
   ; ws                  = ws
   (* Stats *)
   ; tt                  = Timer.create "fixpoint iters"
   ; stat_refines        = ref 0
   ; stat_simple_refines = ref 0
   ; stat_tp_refines     = ref 0
   ; stat_imp_queries    = ref 0
   ; stat_valid_queries  = ref 0
   ; stat_matches        = ref 0
   ; stat_umatches       = ref 0
   ; stat_unsatLHS       = ref 0
   ; stat_emptyRHS       = ref 0
   ; stat_cfreqt         = Hashtbl.create 37
   }, s)
 
(*
  let cs  = BS.time "Simplify" Simplify.simplify_ts cs in 
  let cs' = BS.time "Validation" (PP.validate a s) cs in
  let sri = BS.time "Ref Index" Ci.create ds cs' in
*)
  

(* API *)
let save fname me s =
  let oc  = open_out fname in
  let ppf = F.formatter_of_out_channel oc in
  F.fprintf ppf "@[%a@] \n" Ci.print me.sri;
  F.fprintf ppf "@[%a@] \n" (Misc.pprint_many true "\n" (C.print_wf None)) me.ws;
  F.fprintf ppf "@[%a@] \n" FixSolution.print s;
  close_out oc

(*
(* API *)
let load_soln f =
  let _    = Errorline.startFile f in
  let ic   = open_in f in
  let sols = Lexing.from_channel ic |> FixParse.sols FixLex.token in
  let _    = close_in ic in
  List.fold_left (fun sol (k, ps) -> SM.add k ps sol) SM.empty sols

(***********************************************************************)
(************** FUTURE WORK:  A Parallel Solver ************************)
(***********************************************************************)

let Par.reduce f = fun (x::xs) -> Par.fold_left f x xs

let one_solve sis s = 
  Par.map (fun si -> Solve.solve si s) sis |> 
  Par.reduce (fun (s,b) (s',b') -> (Constraint.join s s', b || b'))

(* API *)
let psolve n ts axs cs s0 = 
  let css = partition cs n in
  let sis = pmap (Solve.create ts axs) css in
  Misc.fixpoint (one_solve sis) s0
*)
