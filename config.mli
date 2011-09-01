(* This module deals with top-level parsing of fq files and such *)


exception UnmappedKvar of Ast.Symbol.t

type qbind = Ast.Qualifier.def list list

type deft = Srt of Ast.Sort.t 
          | Axm of Ast.pred 
          | Cst of FixConstraint.t
          | Wfc of FixConstraint.wf
          | Con of Ast.Symbol.t * Ast.Sort.t
          | Sol of Ast.Symbol.t * (Ast.pred * (string * Ast.Subst.t)) list
          | Qul of Ast.Qualifier.t
          | Dep of FixConstraint.dep

type 'bind cfg = { 
   a    : int                                           (* Tag arity *)
 ; ts   : Ast.Sort.t list                               (* New sorts, now = []*)
 ; ps   : Ast.pred list                                 (* New axioms, now = [] *)
 ; cs   : FixConstraint.t list
 ; ws   : FixConstraint.wf list
 ; ds   : FixConstraint.dep list
 ; qs   : Ast.Qualifier.t list
 ; bm   : 'bind Ast.Symbol.SMap.t                       (* Initial Sol Bindings *)
 ; cons : (Ast.Symbol.t * Ast.Sort.t) list              (* Distinct Constants *)
 ; uops : Ast.Sort.t Ast.Symbol.SMap.t                  (* Uninterpreted Funs *) 
 ; assm : FixConstraint.soln                            (* invariant fixpoint assumption for K *)
}


module type DOMAIN = sig
  type t
  type bind
  val empty        : t 
  (* val meet         : t -> t -> t *)
  val read         : t -> FixConstraint.soln
  val top          : t -> Ast.Symbol.t list -> t
  val refine       : t -> FixConstraint.t -> (bool * t)
  val unsat        : t -> FixConstraint.t -> bool
  val create       : bind cfg -> t
  val print        : Format.formatter -> t -> unit
  val print_stats  : Format.formatter -> t -> unit
  val dump         : t -> unit
  val mkbind       : qbind -> bind
end

val empty     : 'a cfg 
val create    : deft list -> qbind cfg
