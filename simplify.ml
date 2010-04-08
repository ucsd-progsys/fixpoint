module C = FixConstraint
module P = Ast.Predicate
module E = Ast.Expression
module Sy = Ast.Symbol
open Misc.Ops
open Ast

let rec defs_of_pred (em, pm) p = match p with
  | Atom ((Var v, _), Eq, e), _ 
    when not (P.is_tauto p) -> 
      Sy.SMap.add v e em, pm
  | And [Imp ((Bexp (Var v1, _), _), p1), _; 
         Imp (p2, (Bexp (Var v2, _), _)), _], _ 
    when v1 = v2 && p1 = p2 && not(P.is_tauto p) -> 
      edefs, Sy.SMap.add v1 p1 pm
  | And ps, _ -> 
      List.fold_left defs_of_pred (em, pm) ps
  | _ -> em, pm

let rec expr_apply_defs em pm expr = 
  let ef = expr_apply_defs em pm in
  let pf = pred_apply_defs em pm in
  match expr with 
  | Var v, _ when Sy.SMap.mem v em ->
      Sy.SMap.find v em, true
  | Var _, _ | Con _, _ ->
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
  | Ite (p, e1, e2) -> 
      let p', b'   = pf p in
      let e1', b1' = ef e1 in
      let e2', b2' = ef e2 in
      eIte (p', e1', e2'), (b' || b2' || b3')
  | Fld (v, e) -> 
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
  | Atom (e1, brel, e2) ->
      let e1', b1' = ef e1 in
      let e2', b2' = ef e2 in
      pAnd (e1', brel, e2'), b1' || b2'
  | Forall (qs, p) -> 
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
  Misc.fixpoint (expr_apply_defs em fm) e |> fst

let pred_apply_defs em fm p = 
  Misc.fixpoint (pred_apply_defs em fm) f |> fst
 
let subs_apply_defs em pm xes =
  List.map (Misc.app_snd (expr_apply_defs em pm)) xes

let kvar_apply_defs em pm (xes, kvar) = 
  subs_apply_defs em pm xes, kvar 

let preds_kvars_of_reft reft =
  List.fold_left begin fun (ps, ks) -> function 
    | C.Conc p -> p :: ps, ks
    | C.Kvar (xes, kvar) -> ps, (xes, kvar) :: ks 
  end ([], []) (C.ras_of_reft reft)

let simplify_subs xes =
  xes |> List.filter (fun (x, e) -> not (P.is_tauto (pAtom (eVar x, Eq, e))))

let simplify_kvar (xes, kvar) =
  simplify_subs xes, kvar 

(**************** HEREHEREHEREHEREHEREHERE *******************)

let simplify_t t = 
  let env_ps, pfree_env = (* separate concrete predicates from refinement templates *)
    Sy.SMap.fold 
      (fun bv reft (ps, env) -> 
	 let vv = C.vv_of_reft reft in
	 let bv_expr = Ast.eVar bv in
	 let sort = C.sort_of_reft reft in
	 let reft_ps, reft_ks = preds_kvars_of_reft reft in
	   (List.rev_append (List.map (fun p -> P.subst p vv bv_expr) reft_ps) ps,
	    if reft_ks = [] then env else Sy.SMap.add bv (vv, sort, reft_ks) env)
      ) (C.env_of_t t) ([], Sy.SMap.empty) in
  let lhs = C.lhs_of_t t in
  let lhs_vv = C.vv_of_reft lhs in
  let lhs_ps, lhs_ks = preds_kvars_of_reft lhs in
  let body_pred = Ast.pAnd (C.grd_of_t t :: List.rev_append lhs_ps env_ps) in
  let edefs, pdefs = defs_of_pred (Sy.SMap.empty, Sy.SMap.empty) body_pred in
    Printf.printf "\nbody_pred edefs map for %d\n" (C.id_of_t t);
    Sy.SMap.iter (fun v exp ->
		    Printf.printf "%s -> %s\n" (Sy.to_string v) (E.to_string exp)
		 ) edefs;
    Printf.printf "edef for lhs_vv %s = %s (simplified %s)\n" (Sy.to_string lhs_vv) 
      (try Sy.SMap.find lhs_vv edefs |> E.to_string with Not_found -> "none")
      (try Sy.SMap.find lhs_vv edefs |> expr_apply_defs edefs pdefs |> E.to_string with Not_found -> "none");
  let kvar_to_simple_Kvar (subs, sym) = C.Kvar (subs_apply_defs edefs pdefs subs |> simplify_subs, sym) in
  let senv = 
    Sy.SMap.mapi (fun bv (vv, sort, ks) -> 
		    List.map kvar_to_simple_Kvar ks |>	C.make_reft vv sort) pfree_env in
    Printf.printf "body_pred: %s\n" (P.to_string body_pred);
  let sgrd' = pred_apply_defs edefs pdefs body_pred |> Ast.simplify_pred in
  let sgrd = 
    try
      Ast.pAnd [sgrd'; Ast.pAtom (Ast.eVar lhs_vv, Ast.Eq, Sy.SMap.find lhs_vv edefs |> expr_apply_defs edefs pdefs)]
    with Not_found -> sgrd' in
    Printf.printf "simplified body_pred: %s\n" (P.to_string sgrd);
  let slhs = List.map kvar_to_simple_Kvar lhs_ks |> C.make_reft (C.vv_of_reft lhs) (C.sort_of_reft lhs) in
  let rhs = C.rhs_of_t t in
  let rhs_ps, rhs_ks = preds_kvars_of_reft rhs in
  let srhs_pred = pred_apply_defs edefs pdefs (Ast.pAnd rhs_ps) |> Ast.simplify_pred in
  let srhs_ks = List.map kvar_to_simple_Kvar rhs_ks in
  let srhs =  (if P.is_tauto srhs_pred then srhs_ks else (C.Conc srhs_pred) :: srhs_ks) |> 
      C.make_reft (C.vv_of_reft rhs) (C.sort_of_reft rhs) in
    C.make_t senv sgrd slhs srhs (Some (C.id_of_t t)) (C.tag_of_t t)

let simplify_ts ts =
  (* drop t if its rhs is a k variable that is not read *)
  let ts_sofar = ref ts in
  let pruned = ref true in
    while !pruned && !ts_sofar <> [] do
      let pruned_ts, rest_ts = 
	List.partition
	  (fun t ->
	     match C.rhs_of_t t |> preds_kvars_of_reft with
	       | [], [(_, sy)] ->
		   List.for_all 
		     (fun t' -> 
			List.for_all (fun (_, sy') -> sy <> sy') 
			  (Sy.SMap.fold 
			     (fun _ reft sofar -> List.rev_append (C.kvars_of_reft reft) sofar) 
			     (C.env_of_t t') (C.lhs_of_t t' |> C.kvars_of_reft))
		     ) !ts_sofar
	       | _ -> false
	  ) !ts_sofar in
	ts_sofar := rest_ts;
	pruned := pruned_ts <> []
    done;
    !ts_sofar

let is_tauto_t t =
  t |> C.rhs_of_t 
    |> C.ras_of_reft 
    |> (function [C.Conc p] -> P.is_tauto p | [] -> true | _ -> false)
