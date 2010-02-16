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
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONAst.Symbol.
 *
 *)

(* This module implements the IMP language and translation from fixpoint constraints *)


module F  = Format
module H  = Hashtbl
module A  = Ast
module E  = A.Expression
module P  = A.Predicate
module Sy = A.Symbol
module SM = Sy.SMap
module C = FixConstraint
(*module BS = BNstats*)



(* vars are always in lex order *)

type var   = PVar of Sy.t
           | TVar of Sy.t

type decl  = RDecl of Sy.t * var list
           | PDecl of Sy.t

type tupl  = var list

type instr = Assm of A.pred list
           | Asst of A.pred list
           | Asgn of var * var
           | Rget of Sy.t * tupl
           | Rset of tupl * Sy.t

type block = instr list

type program = decl list * block list

let filter_wfs cs =
  Misc.maybe_list (List.map (function Wfc x -> Some x | _ -> None))

let filter_subt cs =
  Misc.maybe_list (List.map (function Cst x -> Some x | _ -> None))

let wf_to_decls wf =
  let vars  = Misc.sort_and_compact (List.map fst (bindings_of_env (C.env_of_wf wf))) in
  let kvars = C.kvars_of_reft (C.reft_of_wf wf) in
  (List.rev_map2 (fun k -> (k, vars)) kvars, List.map (fun v -> PDecl v) vars)

let constraints_to_decls cs =
  let decls = List.map wf_to_decls (filter_wfs cs) in
  let rdecls = Misc.flap snd decls in
  let pdecls = Misc.sort_and_compact (Misc.flap fst decls) in
  rdecls @ pdecls 

let constraints_to_program cs =
  let decls = constraints_to_decls cs in
  (decls, constraints_to_blocks decls cs)

let binding_to_instrs (var, reft) =
  reft_to_get_instrs reft @ [Asgn (PVar var, PVar (vv_of_reft reft))]

let envt_to_instrs envt =
  Misc.flap binding_to_instrs (C.bindings_of_envt envt)

let reft_to_get_instrs decls reft =
  let vv = vv_of_reft reft in
  let kvars = kvars_of_reft reft in
  let preds = preds_of_reft reft in
  match (kvars, preds) with
  | ([], preds) -> Havc vv :: Assm preds :: []
  | (kvars, []) -> Misc.flap (get_instrs vv decls) kvars
  | (kvars, preds) -> Misc.flap (get_instrs vv decls) kvars @ ([Assm preds])

let reft_to_set_instrs decls reft =
  let vv = vv_of_reft reft in
  let kvars = kvars_of_reft reft in
  let preds = preds_of_reft reft in
  match (kvars, preds) with
  | ([], preds) -> Asst preds :: []
  | (kvars, []) -> Misc.flap (set_instrs vv decls) kvars
  | (kvars, preds) -> Misc.flap (get_instrs vv decls) kvars @ ([Asst preds])

let rec get_kdecl kvar decls =
  match decls with  
  | RDecl (k, vars) :: decls ->
      if k = kvar then
        vars
      else
        get_kdecl kvar decls
  | _ :: decls -> get_kdecl kvar decls
  | [] -> raise Not_found

let get_instrs vv decls (subs, kvar) =
  let vars = get_kdecl kvar decls in
  let tvars = List.map (fun v -> TVar v) vars in
  let assumes = List.map (sub_to_assume vars) subs in
  RGet (kvar, tvars) :: assumes @
  [Asgn (PVar vv, TVar (hd vars))]

let sub_to_assume (var, expr) =
  Assm (A.eBin var A.Eq expr)

let set_instrs decls (subs, kvar) =
  RSet (get_kdecls kvar decls, kvar)

let constraints_to_blocks decls cs =
  List.map constraint_to_block (filter_subt cs)

let constraint_to_block c =
  let (env, grd, lhs, rhs) = (C.env_of_t c,
                              C.grd_of_t c,
                              C.vars_of_t c,
                              C.lhs_of_t c,
                              C.rhs_of_t c) in
  envt_to_instrs env @
  [Asst grd] @
  reft_to_get_instrs lhs @
  reft_to_set_instrs rhs

let check_imp prog = true
  
