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

(**
 * This module implements a DAG representation for expressions and 
 * predicates: each sub-predicate or sub-expression is paired with
 * a unique int ID, which enables constant time hashing. 
 * However, one must take care when using DAGS:
 * (1) they can only be constructed using the appropriate functions
 * (2) when destructed via pattern-matching, one must discard the ID
 *)

(*******************************************************)
(********************** Base Logic  ********************)
(*******************************************************)

module Sort :
  sig
    type loc = 
      | Loc  of string 
      | Lvar of int

    type t    
    type sub
    
    val to_string   : t -> string
    val print       : Format.formatter -> t -> unit
    
    val t_obj       : t
    val t_bool      : t
    val t_int       : t
    val t_generic   : int -> t
    val t_ptr       : loc -> t
    val t_func      : int -> t list -> t
   
    val is_bool     : t -> bool
    val is_int      : t -> bool
    val is_func      : t -> bool
    val func_of_t   : t -> (t list * t) option
    val ptr_of_t    : t -> loc option
 
 (* val compat      : t -> t -> bool *)
    val unify       : t list -> t list -> sub option
    val apply       : sub -> t -> t
  end

module Symbol : 
  sig 
    type t 
    module SMap : Map.S with type key = t
    module SSet : Set.S with type elt = t
    val is_wild : t -> bool
    val of_string : string -> t
    val to_string : t -> string 
    val is_wild: t -> bool
    val print : Format.formatter -> t -> unit
    val value_variable : Sort.t -> t
    val is_value_variable : t -> bool
    val sm_length : 'a SMap.t -> int
    val sm_filter : (t -> 'a -> bool) -> 'a SMap.t -> 'a SMap.t
    val sm_to_list : 'a SMap.t -> (t * 'a) list
  end

module Constant :
  sig
    type t = Int of int		
    val to_string : t -> string
    val print : Format.formatter -> t -> unit
  end

type tag  (* externally opaque *)

type brel = Eq | Ne | Gt | Ge | Lt | Le 

type bop  = Plus | Minus | Times | Div
    
type expr = expr_int * tag 
    
and expr_int =
  | Con of Constant.t
  | Var of Symbol.t
  | App of Symbol.t * expr list
  | Bin of expr * bop * expr  
  | Ite of pred * expr * expr
  | Fld of Symbol.t * expr             (* NOTE: Fld (s, e) == App ("field"^s,[e]) *) 
  | Cst of expr * Sort.t   
  | Bot

and pred = pred_int * tag

and pred_int =
  | True
  | False
  | And  of pred list
  | Or   of pred list
  | Not  of pred
  | Imp  of pred * pred
  | Bexp of expr
  | Atom of expr * brel * expr 
  | Forall of ((Symbol.t * Sort.t) list) * pred

(* Constructors : expressions *)
val eCon : Constant.t -> expr
val eVar : Symbol.t -> expr
val eApp : Symbol.t * expr list -> expr
val eBin : expr * bop * expr -> expr 
val eIte : pred * expr * expr -> expr
val eFld : Symbol.t * expr -> expr
val eCst : expr * Sort.t -> expr
(* Constructors : predicates *)
val pTrue  : pred
val pFalse : pred
val pAtom  : expr * brel * expr -> pred
val pAnd   : pred list -> pred
val pOr    : pred list -> pred
val pNot   : pred -> pred
val pImp   : (pred * pred) -> pred
val pIff   : (pred * pred) -> pred
val pBexp  : expr -> pred
val pForall: ((Symbol.t * Sort. t) list) * pred -> pred
val pEqual : expr * expr -> pred

module Expression : 
sig
  module Hash : Hashtbl.S with type key = expr 
  
  val print     : Format.formatter -> expr -> unit
  val show      : expr -> unit
  val to_string : expr -> string
  
  val unwrap    : expr -> expr_int
  val support   : expr -> Symbol.t list
  val subst     : expr -> Symbol.t -> expr -> expr 
  val map       : (pred -> pred) -> (expr -> expr) -> expr -> expr 
  val iter      : (pred -> unit) -> (expr -> unit) -> expr -> unit 
end
 

module Predicate :
sig
  module Hash : Hashtbl.S with type key = pred 
 
  val print     : Format.formatter -> pred -> unit
  val show      : pred -> unit
  val to_string : pred -> string

  val unwrap    : pred -> pred_int
  val support   : pred -> Symbol.t list
  val subst     : pred -> Symbol.t -> expr -> pred
  val map       : (pred -> pred) -> (expr -> expr) -> pred -> pred 
  val iter      : (pred -> unit) -> (expr -> unit) -> pred -> unit 
  val is_contra : pred -> bool
  val is_tauto  : pred -> bool
  (* val size      : pred -> int *)
end

module Qualifier : 
  sig
    type t 
    val create    : Symbol.t -> Sort.t -> pred -> t 
    val vv_of_t   : t -> Symbol.t
    val pred_of_t : t -> pred
    val sort_of_t : t -> Sort.t
    val vv_of_t   : t -> Symbol.t
    val print     : Format.formatter -> t -> unit
  end

module Subst : 
  sig
    type t
    val empty     : t
    val is_empty  : t -> bool
    val extend    : t -> (Symbol.t * expr) -> t
    val concat    : t -> t -> t
    val of_list   : (Symbol.t * expr) list -> t
    val to_list   : t -> (Symbol.t * expr) list
    val print     : Format.formatter -> t -> unit
  end

module Horn :
  sig
    type pr = string * string list
    type gd = C of pred | K of pr
    type t  = pr * gd list 
    val print: Format.formatter -> t -> unit
    val support: t -> string list
  end

val print_stats : unit -> unit
val fixdiv      : pred -> pred
val zero        : expr
val one         : expr
val bot         : expr
val substs_pred    : pred -> Subst.t -> pred 
val simplify_pred  : pred -> pred
val sortcheck_expr : (Symbol.t -> Sort.t) -> expr -> Sort.t option
val sortcheck_pred : (Symbol.t -> Sort.t) -> pred -> bool


