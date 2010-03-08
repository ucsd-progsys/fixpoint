val preds_kvars_of_reft: FixConstraint.reft -> Ast.pred list * (FixConstraint.subs * Ast.Symbol.t) list
val simplify_t: FixConstraint.t -> FixConstraint.t
val is_tauto_t: FixConstraint.t -> bool
