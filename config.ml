module MSM = Misc.StringMap

open Misc.Ops

exception UnmappedKvar of Ast.Symbol.t

type deft = Srt of Ast.Sort.t 
          | Axm of Ast.pred 
          | Cst of FixConstraint.t
          | Wfc of FixConstraint.wf
          | Con of Ast.Symbol.t * Ast.Sort.t
          | Sol of Ast.Symbol.t * (Ast.pred * (string * Ast.Subst.t)) list
          | Qul of Ast.Qualifier.t
          | Dep of FixConstraint.dep

type cfg = { 
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

let get_arity = function
  | []   -> assertf "Fixpoint: NO CONSTRAINTS!"
  | c::_ -> c |> FixConstraint.tag_of_t |> fst |> List.length

let sift_quals ds = 
  ds |> Misc.map_partial (function Qul q -> Some (Ast.Qualifier.name_of_t q, q) | _ -> None)
     >> (List.map fst <+> (fun ns -> asserts (Misc.distinct ns) "ERROR: duplicate quals!"))
     |> MSM.of_list

let extend s2d cfg = function
  | Srt t      -> {cfg with ts   = t     :: cfg.ts   }   
  | Axm p      -> {cfg with ps   = p     :: cfg.ps   } 
  | Cst c      -> {cfg with cs   = c     :: cfg.cs   }
  | Wfc w      -> {cfg with ws   = w     :: cfg.ws   } 
  | Con (s,t)  -> {cfg with cons = (s,t) :: cfg.cons; uops = Ast.Symbol.SMap.add s t cfg.uops} 
  | Dep d      -> {cfg with ds   = d     :: cfg.ds   }
  | Qul q      -> {cfg with qs   = q     :: cfg.qs   }
  | Sol (k,ps) -> {cfg with bs   = (k, s2d ps) :: cfg.bs  }

let empty = {a = 0; ts = []; ps = []; cs = []; ws = []; ds = []; qs = []; bs
= []; cons = []; uops = Ast.Symbol.SMap.empty }

(* API *)
let create ds =
  let qm  = sift_quals ds in
  let n2q = fun n -> Misc.do_catchf ("name2qual: "^n) (MSM.find n) qm in
  let s2d = List.map (fun (p, (n,s)) -> (p, (n2q n, s))) in
  ds |> List.fold_left (extend s2d) empty
     |> (fun cfg -> {cfg with a = get_arity cfg.cs})

module type DOMAIN = sig
  type t
  val empty        : t 
  val read         : t -> FixConstraint.soln
  val top          : t -> Ast.Symbol.t list -> t
  val refine       : t -> FixConstraint.t -> (bool * t)
  val unsat        : t -> FixConstraint.t -> bool
  
  val create       : cfg -> t
  val print        : Format.formatter -> t -> unit
  val print_stats  : Format.formatter -> t -> unit
  val dump         : t -> unit
end

module type SOLVER = sig
  type t
  type soln
  val create    : cfg -> (t * soln)
  val solve     : t -> soln -> (soln * (FixConstraint.t list)) 
  val save      : string -> t -> soln -> unit 
end


type t = cfg
