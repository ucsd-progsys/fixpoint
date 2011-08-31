(* This module deals with top-level parsing of fq files and such *)

type deft = Srt of Ast.Sort.t 
          | Axm of Ast.pred 
          | Cst of FixConstraint.t
          | Wfc of FixConstraint.wf
          | Con of Ast.Symbol.t * Ast.Sort.t
          | Sol of Ast.Symbol.t * (Ast.pred * (string * Ast.Subst.t)) list
          | Qul of Ast.Qualifier.t
          | Dep of FixConstraint.dep

type t = { 
   ts   : Ast.Sort.t list
 ; ps   : Ast.pred list
 ; cs   : FixConstraint.t list
 ; ws   : FixConstraint.wf list
 ; ds   : FixConstraint.dep list
 ; qs   : Ast.Qualifier.t list
 ; s    : (Ast.Symbol.t * FixSolution.def list) list
 ; cons : (Ast.Symbol.t * Ast.Sort.t) list
}

val create : deft list -> t 
