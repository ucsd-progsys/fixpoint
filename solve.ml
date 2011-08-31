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
module Sy = A.Symbol
module SM = Sy.SMap
module C  = FixConstraint
module Ci = Cindex
module PP = Prepass

open Misc.Ops

type t = {
   sri : Ci.t
 ; ws  : C.wf list
 ; tt  : Timer.t
   
 (* Stats *)
 ; stat_refines        : int ref
 ; stat_cfreqt         : (int * bool, int) Hashtbl.t 
 
 (*
 ; stat_simple_refines : int ref 
 ; stat_tp_refines     : int ref 
 ; stat_imp_queries    : int ref 
 ; stat_valid_queries  : int ref 
 ; stat_matches        : int ref 
 ; stat_umatches       : int ref 
 ; stat_unsatLHS       : int ref 
 ; stat_emptyRHS       : int ref 
 *)

}

let mydebug = false 

(*************************************************************)
(********************* Stats *********************************)
(*************************************************************)

let hashtbl_incr_frequency t k = 
  let n = try Hashtbl.find t k with Not_found -> 0 in
  Hashtbl.replace t k (n+1)

let hashtbl_print_frequency t = 
  Misc.hashtbl_to_list t 
  |> Misc.kgroupby (fun ((k,b),n) -> (n,b))
  |> List.map (fun ((n,b), xs) -> (n, b, List.map (fst <+> fst) xs))
  |> List.sort compare
  |> List.iter begin fun (n, b, xs) -> 
       Co.logPrintf "ITERFREQ: %d times (ch = %b) %d constraints %s \n"
         n b (List.length xs) (Misc.map_to_string string_of_int xs) 
     end

(* 
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
    let kqs1    = List.map fst x1 |> List.map Misc.single in
    (if C.is_simple c 
     then (ignore(me.stat_simple_refines += 1); kqs1) 
     else kqs1 ++ (BS.time "check tp" (check_tp me env vv1 t1 lps (FixSolution.p_imp s)) x2))
    |> FixSolution.p_update s k2s 

    *)



(***************************************************************)
(************************ Debugging/Stats **********************)
(***************************************************************)

let print_constr_stats ppf cs = 
  let cn   = List.length cs in
  let scn  = List.length (List.filter C.is_simple cs) in
  F.fprintf ppf "#Constraints: %d (simple = %d) \n" cn scn

let print_solver_stats ppf me = 
  print_constr_stats ppf (Ci.to_list me.sri); 
  F.fprintf ppf "#Iterations = %d\n" !(me.stat_refines);
  F.fprintf ppf "Iteration Frequency: \n"; 
    hashtbl_print_frequency me.stat_cfreqt;
  F.fprintf ppf "Iteration Periods: @[%a@] \n" Timer.print me.tt

let dump me s = 
  Co.cLogPrintf Co.ol_solve_stats "%a \n" print_solver_stats me;
  Co.cLogPrintf Co.ol_solve_stats "%a \n" FixSolution.print_stats s;
  FixSolution.dump_cluster s

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
  qs |> List.filter (fun q -> not (So.unify [t] [Q.sort_of_t q] = None))
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

(***************************************************************)
(******************** Iterative Refinement *********************)
(***************************************************************)

let log_iter_stats me s =
  (if Co.ck_olev Co.ol_insane then Co.logPrintf "%a" FixSolution.print s);
  (if !(me.stat_refines) mod 100 = 0 then 
     let msg = Printf.sprintf "num refines=%d" !(me.stat_refines) in 
     let _   = Timer.log_event me.tt (Some msg) in
     let _   = Co.logPrintf "%s" msg in 
     let _   = Co.logPrintf "%a \n" FixSolution.print_stats s in
     ());
  ()

let rec acsolve me w s =
  let _ = log_iter_stats me s in
  match Ci.wpop me.sri w with 
  | (None,_) -> 
      let _ = Timer.log_event me.tt (Some "Finished") in 
      s 
  | (Some c, w') ->
      let _         = me.stat_refines += 1             in 
      let (ch, s')  = BS.time "refine" (FixSolution.refine s) c in
      let _         = hashtbl_incr_frequency me.stat_cfreqt (C.id_of_t c, ch) in  
      let _         = Co.bprintf mydebug "iter=%d id=%d ch=%b %a \n" 
                      !(me.stat_refines) (C.id_of_t c) ch C.print_tag (C.tag_of_t c) in
      let w'' = if ch then Ci.deps me.sri c |> Ci.wpush me.sri w' else w' in 
      acsolve me w'' s' 

let unsat_constraints me s =
  me.sri |> Ci.to_list |> List.filter (FixSolution.unsat s)




(***************************************************************)
(****************** Pruning Unconstrained Vars *****************)
(***************************************************************)

let rhs_ks cs =
  cs  |> Misc.flap (Misc.compose C.kvars_of_reft C.rhs_of_t)
      |> List.fold_left (fun rhss (_, kv) -> Sy.SSet.add kv rhss) Sy.SSet.empty

let unconstrained_kvars cs =
  let rhss = rhs_ks cs in
  cs  |> Misc.flap C.kvars_of_t
      |> List.map snd
      |> List.filter (fun kv -> not (Sy.SSet.mem kv rhss))

let true_unconstrained sri s =
  sri |> Cindex.to_list 
      |> unconstrained_kvars
      |> FixSolution.top s

(* 
let true_unconstrained sri s = 
  if !Co.true_unconstrained then 
    let _ = Co.logPrintf "Fixpoint: Pruning unconstrained kvars \n" 
    in true_unconstrained sri s
  else 
    let _ = Co.logPrintf "Fixpoint: NOT Pruning unconstrained kvars \n" 
    in s
*)

(* API *)
let solve me s = 
  let _  = Co.logPrintf "Fixpoint: Validating Initial Solution \n" in
  let _  = BS.time "Prepass.profile" PP.profile me.sri in
  let s  = s |> (!Co.true_unconstrained <?> BS.time "Prepass.true_unconstr" (true_unconstrained me.sri)) in
  (* let _  = Co.cprintf Co.ol_insane "%a%a" Ci.print me.sri FixSolution.print s; dump me s in *)
  let _  = Co.logPrintf "Fixpoint: Initialize Worklist \n" in
  let w  = BS.time "Cindex.winit" Ci.winit me.sri in 
  let _  = Co.logPrintf "Fixpoint: Refinement Loop \n" in
  let s  = BS.time "Solve.acsolve"  (acsolve me w) s in
  let _  = BS.time "Solve.dump" (dump me) s in
  let _  = Co.logPrintf "Fixpoint: Testing Solution \n" in
  let u  = BS.time "Solve.unsatcs" (unsat_constraints me) s in
  let _  = if u != [] then F.printf "Unsatisfied Constraints:\n %a" (Misc.pprint_many true "\n" (C.print_t None)) u in
  (s, u)

let ppBinding (k, zs) = 
  F.printf "ppBind %a := %a \n" 
    Sy.print k 
    (Misc.pprint_many false "," P.print) (List.map fst zs)

    (* ORIG
(* API *)
let create ts sm ps a ds consts cs ws bs0 qs =
  let sm  = List.fold_left (fun sm (x,so) -> SM.add x so sm) sm consts in
  let tpc = TP.create ts sm ps (List.map fst consts) in
  let qs  = Q.normalize qs >> Co.logPrintf "Using Quals: \n%a" (Misc.pprint_many true "\n" Q.print) in
  let sri = cs  >> Co.logPrintf "Pre-Simplify Stats\n%a" print_constr_stats 
                |> BS.time  "Constant Env" (List.map (C.add_consts_t consts))
                |> BS.time  "Simplify" FixSimplify.simplify_ts
                >> Co.logPrintf "Post-Simplify Stats\n%a" print_constr_stats
                |> BS.time  "Ref Index" Ci.create ds 
                |> (!Co.slice <?> BS.time "Slice" Ci.slice) in
  let ws  = ws  |> (!Co.slice <?> BS.time "slice_wf" (Ci.slice_wf sri))
                |> BS.time  "Constant EnvWF" (List.map (C.add_consts_wf consts)) 
                |> PP.validate_wfs in
  let bs  = BS.time "Qual Inst" (inst ws) qs (* >> List.iter ppBinding *) in 
  let s   = FixSolution.of_bindings ts sm ps (bs0 ++ bs) in
  let _   = sri |> Ci.to_list |> BS.time "Validate" (PP.validate a s) in
  ({ tpc  = tpc;    sri  = sri;     ws = ws
   (* Stats *)
   ; tt                  = Timer.create "fixpoint iters"
   ; stat_refines        = ref 0; stat_simple_refines = ref 0
   ; stat_tp_refines     = ref 0; stat_imp_queries    = ref 0
   ; stat_valid_queries  = ref 0; stat_matches        = ref 0
   ; stat_umatches       = ref 0; stat_unsatLHS       = ref 0
   ; stat_emptyRHS       = ref 0; stat_cfreqt         = Hashtbl.create 37
   }, s)

  *)


(* API *)
let create ts sm ps a ds consts cs ws bs0 qs =
  let sri = cs  >> Co.logPrintf "Pre-Simplify Stats\n%a" print_constr_stats 
                |> BS.time  "Constant Env" (List.map (C.add_consts_t consts))
                |> BS.time  "Simplify" FixSimplify.simplify_ts
                >> Co.logPrintf "Post-Simplify Stats\n%a" print_constr_stats
                |> BS.time  "Ref Index" Ci.create ds 
                |> (!Co.slice <?> BS.time "Slice" Ci.slice) in
  let ws  = ws  |> (!Co.slice <?> BS.time "slice_wf" (Ci.slice_wf sri))
                |> BS.time  "Constant EnvWF" (List.map (C.add_consts_wf consts)) 
                |> PP.validate_wfs in
 
  let sm  = List.fold_left (fun sm (x,so) -> SM.add x so sm) sm consts in
 
  let s   = qs  |> Q.normalize 
                >> Co.logPrintf "Using Quals: \n%a" (Misc.pprint_many true "\n" Q.print) 
                |> BS.time "Qual Inst" (inst ws)
             (* >> List.iter ppBinding *)
                |> (++) bs0
                |> FixSolution.create ts sm ps consts in
  let _   = sri |> Ci.to_list |> BS.time "Validate" (PP.validate a (FixSolution.read s)) in
  ({     sri  = sri;     ws = ws
   (* Stats *)
   ; tt                  = Timer.create "fixpoint iters"
   ; stat_refines        = ref 0

  
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
