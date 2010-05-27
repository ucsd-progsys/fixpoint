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
 *
 *)

module Co = Constants
module IM = Misc.IntMap
module C  = FixConstraint
module P  = Ast.Predicate
module E  = Ast.Expression
module Sy = Ast.Symbol

open Misc.Ops
open Ast


let mydebug = false

(****************************************************************************)
(************** Generic Simplification/Transformation API *******************)
(****************************************************************************)

module type SIMPLIFIER =
  sig
    val simplify_ts: FixConstraint.t list -> FixConstraint.t list
  end

(****************************************************************************)
(******************* Syntactic Simplification/Transformation API ************)
(****************************************************************************)

module Syntactic : SIMPLIFIER = struct

let defs_of_pred = 
  let rec dofp (em, pm) p = match p with
    | Atom ((Var v, _), Eq, e), _ 
      when not (P.is_tauto p) -> 
        Sy.SMap.add v e em, pm
    | And [Imp ((Bexp (Var v1, _), _), p1), _; 
           Imp (p2, (Bexp (Var v2, _), _)), _], _ 
      when v1 = v2 && p1 = p2 && not(P.is_tauto p) -> 
        em, Sy.SMap.add v1 p1 pm
    | And ps, _ -> 
        List.fold_left dofp (em, pm) ps
    | _ -> em, pm
  in dofp (Sy.SMap.empty, Sy.SMap.empty)

let rec expr_apply_defs em pm expr = 
  let ef = expr_apply_defs em pm in
  let pf = pred_apply_defs em pm in
  match expr with 
  | Var v, _ when Sy.SMap.mem v em ->
      Sy.SMap.find v em, true
  | Var _, _ | Con _, _ | Bot, _ ->
      expr, false
  | App (v, es), _ -> 
      let _  = asserts (not (Sy.SMap.mem v em)) "binding for UF" in
      es |> List.map ef 
         |> List.split 
         |> (fun (es', bs') -> (eApp (v, es'), List.fold_left (||) false bs'))
  | Bin (e1, op, e2), _ -> 
      let e1', b1' = ef e1 in
      let e2', b2' = ef e2 in
      eBin (e1', op, e2'), (b1' || b2')
  | Ite (p, e1, e2), _ -> 
      let p', b'   = pf p in
      let e1', b1' = ef e1 in
      let e2', b2' = ef e2 in
      eIte (p', e1', e2'), (b' || b1' || b2')
  | Fld (v, e), _ -> 
      let e', b' = ef e in
      eFld (v, e'), b'

and pred_apply_defs em pm pred =
  let ef = expr_apply_defs em pm in
  let pf = pred_apply_defs em pm in
  match pred with 
  | And ps, _ -> 
      ps |> List.map pf
         |> List.split
         |> (fun (ps', bs') -> pAnd ps', List.exists id bs') 
  | Or ps, _ -> 
      ps |> List.map pf
         |> List.split
         |> (fun (ps', bs') -> pOr ps', List.exists id bs') 
  | Not p, _ ->
       p |> pf 
         |> Misc.app_fst pNot
  | Imp (p1, p2), _ -> 
      let p1', b1' = pf p1 in
      let p2', b2' = pf p2 in
      pImp (p1', p2'), b1' || b2'
  | Bexp (Var v, _), _ when Sy.SMap.mem v pm ->
      Sy.SMap.find v pm, true
  | Bexp e, _ ->
      e |> ef |> Misc.app_fst pBexp
  | Atom (e1, brel, e2), _ ->
      let e1', b1' = ef e1 in
      let e2', b2' = ef e2 in
      pAtom (e1', brel, e2'), b1' || b2'
  | Forall (qs, p), _ -> 
      assertf "Forall in Simplify!"
  | _ ->
      pred, false

(* Why does this fixpointing terminate?
 * close em, pm under substitution so that
   for all x in dom(em), support(em(x)) \cap dom(em) = empty *)

(* Assume: em is well-formed, 
 * i.e. exists an ordering on vars of dom(em)
 * x1 < x2 < ... < xn s.t. if xj \in em(xi) then xj < xi *)

let expr_apply_defs em fm e = 
  e |> Misc.fixpoint (expr_apply_defs em fm) 
    |> fst

let pred_apply_defs em fm p = 
  p |> Misc.fixpoint (pred_apply_defs em fm) 
    |> fst
    |> simplify_pred

let subs_apply_defs em pm xes =
  List.map (Misc.app_snd (expr_apply_defs em pm)) xes

let print_em_pm t (em, pm) =
  let id   = t |> C.id_of_t in
  let vv   = t |> C.lhs_of_t |> C.vv_of_reft in
  let vve  = try Sy.SMap.find vv em with Not_found -> bot in
  let vve' = expr_apply_defs em pm vve in
  Co.bprintf mydebug "\nbodyp em map for %d\n" id ;
  Sy.SMap.iter (fun x e -> Co.bprintf mydebug "%a -> %a\n" Sy.print x  E.print e) em;
  Co.bprintf mydebug "\nbodyp pm map for %d\n" id ;
  Sy.SMap.iter (fun x p -> Co.bprintf mydebug "%a -> %a\n" Sy.print x  P.print p) pm;
  Co.bprintf mydebug "edef for vv %a = %a (simplified %a)\n" Sy.print vv E.print vve E.print vve'

let preds_kvars_of_env env =
  Sy.SMap.fold begin fun x r (ps, env) -> 
    let vv       = C.vv_of_reft r in
    let xe       = Ast.eVar x in
    let t        = C.sort_of_reft r in
    let rps, rks = C.preds_kvars_of_reft r in
    let ps'      = List.map (fun p -> P.subst p vv xe) rps ++ ps in
    let env'     = (* match rks with [] -> env | _ -> *) Sy.SMap.add x (vv, t, rks) env in
    ps', env'
  end env ([], Sy.SMap.empty)

let simplify_kvar em pm (xes, sym) =
  xes |> subs_apply_defs em pm
      |> List.filter (fun (x,e) -> not (P.is_tauto (pAtom (eVar x, Eq, e))))
      |> (fun xes -> C.Kvar (xes, sym))

let simplify_env em pm ks_env = 
  Sy.SMap.map begin fun (vv, t, ks) -> 
    ks |> List.map (simplify_kvar em pm) |> C.make_reft vv t
  end ks_env

let simplify_grd em pm vv t p =
  let _  = Co.bprintf mydebug "simplify_grd [1]: %a \n" P.print p in
  let p  = pred_apply_defs em pm p in
  let _  = Co.bprintf mydebug "simplify_grd [2]: %a \n" P.print p in
  begin try 
    Sy.SMap.find vv em 
    |> expr_apply_defs em pm
    |> (fun vve -> pAnd [p; pAtom (eVar vv, Eq, vve)])
  with Not_found -> p end
  >> Co.bprintf mydebug "simplify_grd [3]: %a \n" P.print

let simplify_refa em pm = function 
  | C.Conc p          -> C.Conc (pred_apply_defs em pm p) 
  | C.Kvar (xes, sym) -> simplify_kvar em pm (xes, sym)

(* API *)
let simplify_t c = 
  let id             = c |> C.id_of_t in
  let _              = Co.bprintf mydebug "============== Simplifying %d ============== \n"id in
  let env_ps, ks_env = c |> C.env_of_t |> preds_kvars_of_env in
  let l_ps, l_ks     = c |> C.lhs_of_t |> C.preds_kvars_of_reft in
  let vv, t          = c |> C.lhs_of_t |> Misc.tmap2 (C.vv_of_reft, C.sort_of_reft) in
  let bodyp          = Ast.pAnd ([C.grd_of_t c] ++ l_ps ++ env_ps) 
                       >> Co.bprintf mydebug "body_pred: %a \n" P.print in
  let em, pm         = defs_of_pred bodyp                          
                       >> print_em_pm c in

  let senv           = simplify_env em pm ks_env in
  let sgrd           = simplify_grd em pm vv t bodyp in
  let slhs           = l_ks |> List.map (simplify_kvar em pm) |> C.make_reft vv t in
  let srhs           = c |> C.rhs_of_t |> C.ras_of_reft |> List.map (simplify_refa em pm) |> C.make_reft vv t in
  
  C.make_t senv sgrd slhs srhs (C.ido_of_t c) (C.tag_of_t c)

let is_tauto_t c =
  c |> C.rhs_of_t 
    |> C.ras_of_reft 
    |> (function [] -> true | [C.Conc p] -> P.is_tauto p | _ -> false)

(* API *)
let simplify_ts cs = 
  cs |> List.map simplify_t
     |> List.filter (not <.> is_tauto_t) 
end

module Cone : SIMPLIFIER = struct
  let simplify_ts cs =
    let cm = List.fold_left (fun cm c -> IM.add (C.id_of_t c) c cm) IM.empty cs in 
    Kvgraph.create ()
    >> Kvgraph.add cs
    >> Kvgraph.print_stats
    |> Kvgraph.cone_ids 
    |> List.map (fun id -> IM.find id cm)
end

(* API *)
let simplify_ts cs =
  cs |> Syntactic.simplify_ts
     |> Cone.simplify_ts
