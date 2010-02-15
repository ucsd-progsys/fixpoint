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
module BS = BNstats

type program = rdecl list * block list

type block = instr list

(* vars are always in lex order *)

type decl  = RDecl of A.Sy * var list
           | PDecl of A.Sy

type var   = PVar of A.Sy
           | TVar of A.Sy

type tupl  = var list

type cond  = A.Pred

type instr = Assm of bexpr list
           | Asst of bexpr list
           | Asgn of var * var
           | Rget of A.Sy * tupl
           | Rset of tupl * A.Sy

let constraints_to_program cs =
  let decls = constraints_to_decls cs in
  (decls, constraints_to_blocks decls cs)

let constraints_to_decls cs =
  let decls = List.map wf_to_decls (filter_wfs cs) in
  let rdecls = Misc.flap snd decls in
  let pdecls = Misc.sort_and_compact (Misc.flap fst decls) in

let wf_to_decls wf =
  let vars  = Misc.sort_and_compact (List.map fst (bindings_of_env (C.env_of_wf wf))) in
  let kvars = C.kvars_of_reft (C.reft_of_wf wf) in
   (List.rev_map2 (fun k -> (k, vars)) kvars, List.map (fun v -> PDecl v) vars)

let filter_wfs cs =
  Misc.maybe_list (List.map (function Wfc x -> Some x | _ -> None))

let filter_subt cs =
  Misc.maybe_list (List.map (function Cst x -> Some x | _ -> None))

let binding_to_instrs (var, reft) =
  reft_to_instrs reft @ [Asgn (PVar var, PVar (vv_of_reft reft))]

let reft_to_instrs decls reft =
  let vv = vv_of_reft reft in
  let kvars = kvars_of_reft reft in
  let preds = preds_of_reft reft in
  match (kvars, preds) with
  | ([], preds) -> Havc vv :: Assm preds :: []
  (*| (kvars, []) -> Misc.flap (get_instrs vv decls) kvars
  | (kvars, preds) -> assert false*)

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
  get_prologue vars (subs, kvar) @ [Asgn (PVar vv, TVar (hd vars))]

let get_prologue vars (subs, kvar) =
  let vars = List.assoc kvar decls in
  let 
  let assumes = List.map (sub_to_assume vars) subs in

(*let set_instrs decls (subs, kvar) =*)
  

let sub_to_assume (var, expr) =
  Assm (A.eBin var A.Eq expr)

let constraints_to_blocks decls cs =
  List.map constraint_to_block (filter_subt cs)

let constraint_to_block c =
  let env = C.env_of_t c in
  let vars = vars_of_t
