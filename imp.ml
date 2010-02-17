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

(* This module implements translation from fixpoint constraints
 * to IMP commands *)


module F  = Format
module H  = Hashtbl
module A  = Ast
module E  = A.Expression
module P  = A.Predicate
module Sy = A.Symbol
module SM = Sy.SMap
module C = FixConstraint
(*module BS = BNstats*)

open Misc.Ops


(* vars are always in lex order *)

(* We can have at most one set of temporaries in scope at a time
 * so we share names and mark temporaries *)

type var   = PVar of Sy.t
           | TVar of Sy.t

type kvar  = C.subs * Sy.t

type decl  = RDecl of Sy.t * Sy.t list
           | PDecl of Sy.t

(* IMP commands *)

type tupl  = var list

type instr = Assm of A.pred list
           | Asst of A.pred list
           | Asgn of var * var
           | Rget of Sy.t * tupl
           | Rset of tupl * Sy.t
           | Havc of var

type block = instr list

type program = decl list * block list

(* IMP printing *)

let print_var ppf = function 
  | PVar v -> F.fprintf ppf "%a" Sy.print v
  | TVar v -> F.fprintf ppf "'%a" Sy.print v

let print_tuple ppf =
  F.fprintf ppf "(%a)" (Misc.pprint_many false ", " print_var)

let print_instr ppf = function
  | Assm ps ->
      F.fprintf ppf "@[assume@ (%a);@]"
        (Misc.pprint_many false ", " A.Predicate.print) ps
  | Asst ps ->
      F.fprintf ppf "@[assert@ (%a);@]"
        (Misc.pprint_many false ", " A.Predicate.print) ps
  | Asgn (lhs, rhs) ->
      F.fprintf ppf "@[%a@ :=@ %a;@]" print_var lhs print_var rhs
  | Rget (rv, tupl) ->
      F.fprintf ppf "@[%a@ <|@ %a;@]" print_tuple tupl Sy.print rv
  | Rset (tupl, rv) ->
      F.fprintf ppf "@[%a@ |>@ %a;@]" print_tuple tupl Sy.print rv
  | Havc v ->
      F.fprintf ppf "@[havoc@ %a;@]" print_var v 
