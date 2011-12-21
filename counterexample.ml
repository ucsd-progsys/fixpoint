(*
 * Copyright © 2009-12 The Regents of the University of California. All rights reserved. 
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
 *
 *)

(***************************************************************)
(* Counterexample Generation (cf. Lahiri-Vanegue, VMCAI 2011) **) 
(***************************************************************)

module F  = Format
module BS = BNstats
module C  = FixConstraint
module IM = Misc.IntMap
module IS = Misc.IntSet
module A  = Ast
module Sy = A.Symbol
module SM = Sy.SMap 
module SS = Sy.SSet
module P  = A.Predicate
module Su = A.Subst
module Q  = Qualifier
module TP  = TpNull.Prover

open Misc.Ops

let mydebug   = false


(***************************************************************************)
(************** Type Aliases ***********************************************)
(***************************************************************************)

type kvar  = Sy.t
type fact  = Abs of kvar * Qualifier.t | Conc of C.id
type cause = step * C.id * ((Sy.t * fact) list)
type step  = int

(* [k |-> [(i0, [q_i0_1...]),...]] 
 * where q_i0_1... are killed at timestep i0 for kvar k sorted by step *)
type lifespan = (step * Q.t list) list SM.t 

(* [id |-> i0,...] 
 * where the constraint id is selected at steps i0... by solver *)
type ctrace  = step list IM.t 

(* [((x1,k1,q1), c1);...;((xn,kn,qn),cn)] 
 * where each k_i+1, q_i+1, c_i+1 is the "cause" for why k_i, q_i is killed *)
type cex     = (Sy.t * fact * C.id) list

let print_fact ppf = function
  | Abs (k, q) -> F.fprintf ppf "%a/%a" Sy.print k Q.print_args q
  | Conc i     -> F.fprintf ppf "%d" i

let print_step ppf (x, f, cid) =
  F.fprintf ppf "%a: %a @@ %d" Sy.print x print_fact f cid

let print_cex = 
  Misc.pprint_many_box true "     " "---> " "" print_step

let compare_fact f1 f2 =
  compare (Misc.fsprintf print_fact f1) (Misc.fsprintf print_fact f2)

module FactMap = Misc.EMap (struct 
  type t = fact
  let compare = compare_fact
  let print   = print_fact
end)

type t = { tpc      : TP.t 
         ; n        : int                          (* number of solver iters *)
         ; s        : FixConstraint.soln
         ; cm       : FixConstraint.t IM.t
         ; ctrace   : ctrace 
         ; lifespan : lifespan                     (* builds soln at n                *)
         ; sfm      : fact list IM.t               (* step |-> facts killed at a step *)
         
         ; fsm      : step FactMap.t               (* fact |-> step at which killed   *)
         ; scm      : int IM.t                     (* step |-> constr at step         *)
         }

let scm_of_ctrace = 
  ctrace 
  |> IM.to_list 
  |> Misc.flap (fun (cid, is) -> List.map (fun i -> (i, cid)) is)
  |> Misc.fsort fst
  |> IM.of_list

let fsm_of_lifespan lifetime =
  SM.fold begin fun k sqs fsm ->
    List.fold_left begin fun fsm (step, q) -> 
      FactMap.add (Abs (k, q)) step fsm
    end fsm sqs
  end lifetime FactMap.empty 

(* YUCK *)
let sfm_of_lifespan lifespan : fact list IM.t  = 
  lifespan 
  |> SM.to_list 
  |> Misc.flap begin fun (k, iqss) ->
       List.map begin fun (i, qs) -> 
         (i, List.map (fun q -> Abs (k, q)) qs)
       end iqss
     end
  |> List.fold_left (fun m (i, fs) -> IM.adds i fs m) IM.empty 


(***************************************************************************)
(************** Helpers to Reconstitute Solutions and Candidates ***********)
(***************************************************************************)

let constrOfId me cid = 
   IM.safeFind cid me.cm "Cex.constrOfId"

let solutionAt me n k =
  SM.safeFind k me.lifespan "solutionAt: bad kvar"
  |> List.filter (fun (m,_) -> n <= m) 
  |> Misc.flap snd
  |> Misc.map Q.pred_of_t
  |> (++) (me.s k)

let delta me c n k : fact list = 
  let _n = prevStep me c n in
  SM.safeFind k me.lifespan "delta: bad kvar" 
  |> List.filter (fun (m,_) -> _n <= m && m < n) 
  |> Misc.flap snd
  |> Misc.map (fun q -> Abs (k, q))

(************************************************************************)
(************************************************************************)
(************************************************************************)



(* YUCK: TODO, share with PredAbs *)
let check_tp me env vv t lps =  function [] -> [] | rcs ->
  let env = SM.map snd3 env |> SM.add vv t in
  TP.set_filter me.tpc env vv lps (fun _ _ -> false) rcs 
  |>: List.hd

let isUnsatAt me c n = 
  let s        = solutionAt me n     in
  let env      = C.env_of_t c        in
  let (vv,t,_) = C.lhs_of_t c        in
  let lps      = C.preds_of_lhs s c  in
  let rhsp     = c |> C.rhs_of_t |> C.preds_of_reft s |> A.pAnd in
  not ((check_tp me env vv t lps [(0, rhsp)]) = [0])

let prevStep_conc me c : int =
  let _  = asserts (C.is_conc_rhs c) in
  let no = Misc.find_first_true (isUnsatAt me c) 0 me.n in
  Misc.maybe_apply (+) no (-1)

let prevStep_abs me cid n : int = 
  let rec go n = function
    | m1 :: _ when m1 = n     -> (-1)
    | m1 :: (m2 :: _ as rest) -> if n = m2 then m1 else go n rest
    | _                       -> assertf "prevStep with bad ctrace"
  in go n (IM.safeFind cid me.ctrace "prevStep: bad cid") 

let prevStep me c n = 
  if C.is_conc_rhs c then 
    prevStep_conc me c
  else
    prevStep_abs me (C.id_of_t) n

let killStep me f = 
  FactMap.safeFind f me.fsm "Cex.killStep"

(************************************************************************)
(************************************************************************)
(************************************************************************)

let killerCands me c n : (int * (((Sy.t * fact) * A.pred)) list) list =
  foreach (C.kbindings_of_lhs c) begin fun (x, (vv, t, ras)) ->
    foreach ras begin function C.Kvar (su, k) ->
      foreach (delta me c n k) begin function (Abs (_, q) as f) ->
        let su' = Su.extend su (vv, A.eVar x)       in
        let p'  = A.substs_pred (Q.pred_of_t q) su' in 
        (x, f), p'
      end
    end |> Misc.flatten
  end |> Misc.flatten
  |> Misc.kgroupby (fst <+> snd <+> killStep me)

(* {{{ EAGER
let rhs_pred_of_conc c =
  let _ = asserts (C.is_conc_rhs c) in
  c |> C.rhs_of_t 
    |> thd3 
    |> Misc.map_partial (function C.Conc p -> Some p | _ -> None) 
    |> A.pAnd

let killedsAt me c n : (fact * A.pred) list =
  match C.rhs_of_t c with
  | (_,_, [C.Kvar (su, k)]) ->
      foreach (IM.finds n me.sfm) begin function
        | Abs (_, q) as f -> (f, A.substs_pred (Q.pred_of_t q) su)
      end
  | (_,_, [C.Conc p]) ->
      [(Conc (C.id_of_t c), p)]
  | _ -> failwith "killedsAt"
}}} *)

(************************************************************************)
(************************************************************************)
(************************************************************************)

let print_fact_causes n ppf (f, xfs) =
  F.fprintf ppf "fact %a killed at %d by: %a \n"
    print_fact f
    n
    (Misc.pprint_many_brackets false  (Misc.pprint_tuple Sy.print print_fact)) xfs

let is_bot_killer = function
  | (f, p) when P.is_contra p -> Some f
  | _                         -> None

(* EAGER {{{

let setCause n cid me ((f: fact), (causes: (Sy.t * fact) list)) : t = 
  match causes with
  | [] -> me
  | _  -> { me with ffm = FactMap.safeAdd f (n, cid, causes) me.ffm "Cex.setCause"}


let getKillers_step me _n n c =
  let cid = C.id_of_t c in
  let _   = F.printf "\nsetKillers_step: _n = %d n = %d cid = %d\n" _n n cid in
  let killers = killerCands me c _n n in 
  let killeds = killedsAt me c n      in
  match Misc.exists_maybe is_bot_killer killers with 
  | Some y -> 
      List.map (fun (x,_) -> (x, [y])) killeds
  | None when (killers = []) -> 
      List.map (fun (x,_) -> (x, [])) killeds
  | None -> 
      let _ = F.printf "\nNON BOT KILLER at _n = %d n = %d cid = %d \n" _n n cid in
      let bgp = A.pAnd <| C.preds_of_lhs (solutionAt me n) c in
      TP.unsat_core me.tpc (C.senv_of_t c) bgp killers killeds


let setKillers_step me _n n c = 
  getKillers_step me _n n c
  >> (F.printf "causes:\n%a" (Misc.pprint_many true "\n" (print_fact_causes n)))
  |> List.fold_left (setCause n (C.id_of_t c)) me 

let setKillers_ctrace ctrace me =
  ctrace 
  |> IM.to_list 
  |> Misc.flap (fun (cid, is) -> List.map (fun i -> (i, cid)) is)
  |> Misc.fsort fst
  |> List.fold_left begin fun me (n, cid) -> 
      let c  = constrOfId me cid                in
      let _n = prevStep_abs me (C.id_of_t c) n  in
      setKillers_step me _n n c
     end me

let setKillers_unsats ucs me =
  List.fold_left begin fun me c ->
    setKillers_step me (prevStep_conc me c) me.n c
  end me ucs
}}} *)

(********************************************************************)
(*********************** API ****************************************)
(********************************************************************)

(* API *)
let create s cs ctrace lifespan tpc =
  let scm    = scm_of_ctrace ctrace in
  { tpc      = tpc 
  ; s        = s 
  ; cm       = cs |>: Misc.pad_fst C.id_of_t |> IM.of_list 
  ; n        = 1 + Misc.list_max 0 (IM.domain scm)
  ; ctrace   = IM.map Misc.sort_and_compact ctrace 
  ; lifespan = lifespan
  ; fsm      = fsm_of_lifespan lifespan
  ; scm      = scm
  }  

(* EAGER {{{
(* API *)
let create s cs ucs ctrace lifespan tpc =
  create_ s cs ctrace lifespan tpc
  |> setKillers_ctrace ctrace
  |> setKillers_unsats ucs

(* API *)
let explain me c = 
  let rec go acc f = 
    match FactMap.maybe_find f me.ffm with
    | Some (_, cid, ((x, f') :: _)) -> go ((x, f', cid) :: acc) f'
    | None                          -> acc
  in go [] (Conc (C.id_of_t c))

}}} *)

(*****************************************************************)
(**************** Lazy Explanations ******************************)
(*****************************************************************)

let killedPred me c f =  
  match f, C.rhs_of_t c with
  | Abs (k, q), (_,_, [C.Kvar (su, k')])
    when k = k'
    -> A.substs_pred (Q.pred_of_t q) su
  | Conc cid, (_,_,[C.Conc p])
    when C.id_of_t c = cid
    -> p 
  | _ -> failwith "Counterexample.killed"

let getKillStep me c bgp iks : int =
  let iks = Misc.fsort iks in
  let ps  = iks |>: (snd <+> List.map snd <+> A.pAnd) in
  match TP.unsat_suffix me.tpc (C.senv_of_t c) bgp ps with
  | None   -> E.s <| E.error "getKillStep" 
  | Some j -> List.nth iks j 

let getKillers_cands me c bgp cands =
  match cands, Misc.exists_maybe is_bot_killer cands with 
  | [], _ ->
      None
  | _, Some g -> 
      Some g 
  | _, _  -> begin
      let _ = F.printf "\nNON BOT KILLER at _n = %d n = %d cid = %d \n" _n n cid in
      TP.unsat_core me.tpc (C.senv_of_t c) bgp killers
      |> Misc.do_catch "ERROR: empty unsat core" List.hd

let getKillers_fact (me: t) (f: fact) = 
  let n          = killstep_of_fact me f                    in 
  let cid        = IM.safeFind n me.scm  "Cex.getKillers 2" in
  let c          = IM.safeFind cid me.cm "Cex.getKillers 3" in
  let bgps       = C.preds_of_lhs (solutionAt me n) c
                   |> (++) (A.pNot (killedPred me c f))     in
  let iks        = killerCands me c n                       in
  let (j, cands) = getKillStep me c (A.pAnd bgps) iks       in
  let bgps'      = iks 
                   |> List.filter (fun (i,_) -> j < i)
                   |> Misc.flap   (snd <+> List.map snd)    in 
  (cid, killer_of_cands me c (A.pAnd (bgps ++ bgps')) cands)

let rec explain me acc f = 
  match getKillers_fact me f with
  | cid, Some (x', f') -> explain me ((x', f', cid) :: acc) f' 
  | _  , None          -> acc

let explain me c = 
  explain me [] (Conc (C.id_of_t c))
