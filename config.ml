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
 *)


module MSM = Misc.StringMap
module SM  = Ast.Symbol.SMap
module Q   = Ast.Qualifier
module C   = FixConstraint

open Misc.Ops

exception UnmappedKvar of Ast.Symbol.t


type qbind = Q.def list list

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
 ; bm   : 'bind SM.t                       (* Initial Sol Bindings *)
 (* ; bs   : (Ast.Symbol.t * Ast.Qualifier.def list) list  -- Initial Sol Bindings *)
 ; cons : (Ast.Symbol.t * Ast.Sort.t) list              (* Distinct Constants *)
 ; uops : Ast.Sort.t Ast.Symbol.SMap.t                  (* Uninterpreted Funs *)
 ; assm : FixConstraint.soln
          (* Seed Solution -- must be a fixpoint over constraints *)
}

let get_arity = function
  | []   -> Constants.logPrintf "WARNING: NO CONSTRAINTS!"; 0
  | c::_ -> c |> FixConstraint.tag_of_t |> fst |> List.length

let qual_rename i q = 
  Q.rename ((Q.name_of_t q)^(string_of_int i)) q

(*
let sift_quals ds = 
  ds |> Misc.map_partial (function Qul q -> Some q | _ -> None)
     |> List.fold_left begin fun (i, m) q -> 
          let n       = Q.name_of_t q in
          let (i',q') = if MSM.mem n m then (i+1, qual_rename i q) else (i, q) in
          (i', MSM.add (Q.name_of_t q') q' m)
        end (0, MSM.empty)
     >> (fun (i, _) -> if i <> 0 then Constants.logPrintf "WARNING: duplicate qualifier names")
     |> snd
*)

let sift_quals ds = 
  ds |> Misc.map_partial (function Qul q -> Some q | _ -> None)
     |> Ast.Qualifier.normalize 
     |> Misc.map (Misc.pad_fst Ast.Qualifier.name_of_t)
     |> MSM.of_list

let extend s2d cfg = function
  | Srt t      -> {cfg with ts   = t     :: cfg.ts   }   
  | Axm p      -> {cfg with ps   = p     :: cfg.ps   } 
  | Cst c      -> {cfg with cs   = c     :: cfg.cs   }
  | Wfc w      -> {cfg with ws   = w     :: cfg.ws   } 
  | Con (s,t)  -> {cfg with cons = (s,t) :: cfg.cons; uops = SM.add s t cfg.uops} 
  | Dep d      -> {cfg with ds   = d     :: cfg.ds   }
  | Qul q      -> {cfg with qs   = q     :: cfg.qs   }
  | Sol (k,ps) -> {cfg with bm   = SM.add k (s2d ps) cfg.bm  }

let empty = { a    = 0 ; ts   = []; ps = []
            ; cs   = []; ws   = []; ds = []
            ; qs   = []; bm   = SM.empty
            ; cons = []; uops = SM.empty 
            ; assm = FixConstraint.empty_solution }


(* API *)
let create ds =
  let qm  = sift_quals ds in
  let n2q = fun n -> Misc.do_catchf ("name2qual: "^n) (MSM.find n) qm in
  let s2d = List.map (fun (p, (n,s)) -> [(p, (n2q n, s))]) in
  ds |> List.fold_left (extend s2d) empty
     |> (fun cfg -> {cfg with a  = get_arity cfg.cs})
     |> (fun cfg -> {cfg with ws = C.add_wf_ids cfg.ws})

module type DOMAIN = sig
  type t
  type bind
  val empty        : t 
  (* val meet         : t -> t -> t *)
  val min_read     : t -> FixConstraint.soln
  val read         : t -> FixConstraint.soln
  val read_bind    : t -> Ast.Symbol.t -> bind
  val top          : t -> Ast.Symbol.t list -> t
  val refine       : t -> FixConstraint.t -> (bool * t)
  val unsat        : t -> FixConstraint.t -> bool
  val create       : bind cfg -> FixConstraint.soln option -> t
  val print        : Format.formatter -> t -> unit
  val print_stats  : Format.formatter -> t -> unit
  val dump         : t -> unit
  val mkbind       : qbind -> bind
end

(* type t = Ast.Qualifier.def list list cfg *)

let print ppf me = 
  (* Print cs *)
  Format.fprintf ppf "@[%a@] \n" (Misc.pprint_many true "\n" (C.print_t None)) me.cs;
  (* Print ws *)
  Format.fprintf ppf "@[%a@] \n" (Misc.pprint_many true "\n" (C.print_wf None)) me.ws;
  (* Print qs *)
  Format.fprintf ppf "@[%a@] \n" (Misc.pprint_many true "\n" Q.print) (Q.normalize me.qs)

