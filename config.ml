module MSM = Misc.StringMap

open Misc.Ops

type deft = Srt of Ast.Sort.t 
          | Axm of Ast.pred 
          | Cst of FixConstraint.t
          | Wfc of FixConstraint.wf
          | Con of Ast.Symbol.t * Ast.Sort.t
          | Sol of Ast.Symbol.t * (Ast.pred * (string * Ast.Subst.t)) list
          | Qul of Ast.Qualifier.t
          | Dep of FixConstraint.dep

type t = { 
   ts : Ast.Sort.t list
 ; ps : Ast.pred list
 ; cs : FixConstraint.t list
 ; ws : FixConstraint.wf list
 ; ds : FixConstraint.dep list
 ; qs : Ast.Qualifier.t list
 ; s  : (Ast.Symbol.t * FixSolution.def list) list
 ; cons : (Ast.Symbol.t * Ast.Sort.t) list
}

let sift_quals ds = 
  ds |> Misc.map_partial (function Qul q -> Some (Ast.Qualifier.name_of_t q, q) | _ -> None)
     >> (List.map fst <+> (fun ns -> asserts (Misc.distinct ns) "ERROR: duplicate quals!"))
     |> MSM.of_list

(* API *)
let create ds =
  let qm  = sift_quals ds in
  let n2q = fun n -> Misc.do_catchf ("name2qual: "^n) (MSM.find n) qm in
  let s2d = List.map (fun (p, (n,s)) -> (p, (n2q n, s))) in
  List.fold_left begin fun a -> function 
    | Srt t      -> {a with ts   = t     :: a.ts   }   
    | Axm p      -> {a with ps   = p     :: a.ps   } 
    | Cst c      -> {a with cs   = c     :: a.cs   }
    | Wfc w      -> {a with ws   = w     :: a.ws   } 
    | Con (s,t)  -> {a with cons = (s,t) :: a.cons } 
    | Dep d      -> {a with ds   = d     :: a.ds   }
    | Qul q      -> {a with qs   = q     :: a.qs   }
    | Sol (k,ps) -> {a with s    = (k, s2d ps) :: a.s  }
  end {ts = []; ps = []; cs = []; ws = []; ds = []; qs = []; s = []; cons = [] } ds 


