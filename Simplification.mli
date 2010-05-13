
val simplify_t  : FixConstraint.t -> FixConstraint.t
val simplify_ts : FixConstraint.t list -> FixConstraint.t list
val is_tauto_t  : FixConstraint.t -> bool

val preds_kvars_of_reft : FixConstraint.reft -> (Ast.pred list * (FixConstraint.subs * Ast.Symbol.t) list)
