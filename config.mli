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
   a    : int                                           (* Tag arity *)
 ; ts   : Ast.Sort.t list                               (* New sorts, now = []*)
 ; ps   : Ast.pred list                                 (* New axioms, now = [] *)
 ; cs   : FixConstraint.t list
 ; ws   : FixConstraint.wf list
 ; ds   : FixConstraint.dep list
 ; qs   : Ast.Qualifier.t list
 ; bs   : (Ast.Symbol.t * Ast.Qualifier.def list) list  (* Initial Sol Bindings *)
 ; cons : (Ast.Symbol.t * Ast.Sort.t) list              (* Distinct Constants *)
 ; uops : Ast.Sort.t Ast.Symbol.SMap.t                  (* Uninterpreted Funs *) 
}

val empty     : t 
val create    : deft list -> t 
