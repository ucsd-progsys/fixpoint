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
 * TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONSy.
 *
 *)

(* This module implements basic datatypes and operations on constraints *)
module F  = Format
module H  = Hashtbl
module A  = Ast
module E  = A.Expression
module P  = A.Predicate
module Sy = A.Symbol
module SM = Sy.SMap
module BS = BNstats
module Su = Ast.Subst
module MSM = Misc.StringMap
open Misc.Ops




type tag  = int list * string
type id   = int
type dep  = Adp of tag * tag | Ddp of tag * tag | Ddp_s of tag | Ddp_t of tag

type refa = Conc of A.pred | Kvar of Su.t * Sy.t
type reft = Sy.t * A.Sort.t * refa list                (* { VV: t | [ra] } *)
type envt = reft SM.t
type wf   = envt * reft * (id option) * (A.Qualifier.t -> bool)
type t    = { full    : envt; 
              nontriv : envt;
              guard   : A.pred;
              lhs     : reft;
              rhs     : reft;
              ido     : id option;
              tag     : tag; }

type deft = Srt of Ast.Sort.t 
          | Axm of Ast.pred 
          | Cst of t
          | Wfc of wf
          | Con of Ast.Symbol.t * Ast.Sort.t
          | Sol of Ast.Symbol.t * (Ast.pred * (string * Ast.Subst.t)) list
          | Qul of Ast.Qualifier.t
          | Dep of dep

type config = { 
   ts : Ast.Sort.t list
 ; ps : Ast.pred list
 ; cs : t list
 ; ws : wf list
 ; ds : dep list
 ; qs : Ast.Qualifier.t list
 ; s  : (Ast.Symbol.t * FixSolution.def list) list
 ; cons : (Ast.Symbol.t * Ast.Sort.t) list
}

let mydebug = false 

(*************************************************************)
(************************** Misc.  ***************************)
(*************************************************************)

let sift_quals ds = 
  ds |> Misc.map_partial (function Qul q -> Some (Ast.Qualifier.name_of_t q, q) | _ -> None)
     >> (List.map fst <+> (fun ns -> asserts (Misc.distinct ns) "ERROR: duplicate quals!"))
     |> MSM.of_list

(* API *)
let sift ds =
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




let is_simple_refatom = function 
  | Kvar (s, _) -> Ast.Subst.is_empty s 
  | _           -> false

(* API *)
let fresh_kvar = 
  let tick, _  = Misc.mk_int_factory () in
  tick <+> string_of_int <+> (^) "k_" <+> Sy.of_string

(* API *)
let kvars_of_reft (_, _, rs) =
  Misc.map_partial begin function 
    | Kvar (subs, k) -> Some (subs,k) 
    | _              -> None 
  end rs

let meet x (v1, t1, ra1s) (v2, t2, ra2s) = 
  asserts (v1=v2 && t1=t2) "ERROR: FixConstraint.meet x=%s (v1=%s, t1=%s) (v2=%s, t2=%s)" 
  (Sy.to_string x) (Sy.to_string v1) (A.Sort.to_string t1) (Sy.to_string v2) (A.Sort.to_string t2) ;
  (v1, t1, Misc.sort_and_compact (ra1s ++ ra2s))

let env_of_bindings xrs =
  List.fold_left begin fun env (x, r) -> 
    let r = if SM.mem x env then meet x r (SM.find x env) else r in
    SM.add x r env
  end SM.empty xrs

let bindings_of_env env = 
  SM.fold (fun x y bs -> (x,y)::bs) env []

(* API *)
let is_simple {lhs = (_,_,ra1s); rhs = (_,_,ra2s)} = 
  List.for_all is_simple_refatom ra1s 
  && List.for_all is_simple_refatom ra2s 
  && !Constants.simple

(* API *)
let kvars_of_t {nontriv = env; lhs = lhs; rhs = rhs} =
  [lhs; rhs] 
  |> SM.fold (fun _ r acc -> r :: acc) env
  |> Misc.flap kvars_of_reft 



(*************************************************************)
(*********************** Logic Embedding *********************)
(*************************************************************)

let non_trivial env = 
  SM.fold begin fun x r sm -> match thd3 r with 
        | [] -> sm 
        | _::_ -> SM.add x r sm
  end env SM.empty

(* API *)
let is_conc_refa = function
  | Conc _ -> true
  | _      -> false

(* API *)
let preds_of_refa s   = function
  | Conc p      -> [p]
  | Kvar (su,k) -> k |> FixSolution.read s 
                     |> List.map (Misc.flip A.substs_pred su)

(* API *)
let preds_of_reft s (_,_,ras) =
  Misc.flap (preds_of_refa s) ras

(* API *)
let apply_solution s (v, t, ras) = 
  let ras' = Misc.map (fun ra -> Conc (A.pAnd (preds_of_refa s ra))) ras in
  (v, t, ras')


let preds_of_envt s env =
  SM.fold
    (fun x ((vv, t, ras) as r) ps -> 
      let vps = preds_of_reft s r in
      let xps = List.map (fun p -> P.subst p vv (A.eVar x)) vps in
      xps ++ ps)
    env [] 

(* API *)
let preds_of_lhs s {nontriv = env; guard = gp; lhs =  r1} = 
  let envps = preds_of_envt s env in
  let r1ps  = preds_of_reft s r1 in
  gp :: (envps ++ r1ps) 

(* API *)
let vars_of_t s ({rhs = r2} as c) =
  (preds_of_reft s r2) ++ (preds_of_lhs s c)
  |> Misc.flap P.support

(*
(**************************************************************)
(*******************Constraint Simplification *****************)
(**************************************************************)

let is_var_def v = function
  | Conc (A.Atom ((A.Var x, _), A.Eq, (A.Var y, _)), _) when x = v -> Some y
  | Conc (A.Atom ((A.Var x, _), A.Eq, (A.Var y, _)), _) when y = v -> Some x
  | _                                                              -> None

let str_reft env r = 
  Misc.expand begin fun (v, t, ras) ->
    ras |> List.partition (function Conc _ -> true | _ -> false)
        |> Misc.app_fst (Misc.map_partial (is_var_def v))
        |> Misc.app_fst (List.filter (fun x -> SM.mem x env))
        |> Misc.app_fst (List.map (fun x -> SM.find x env))
  end [r] []

let strengthen_reft env ((v,t,ras) as r) =
  if not !Constants.simplify_t then r else
    let kras = str_reft env r in
    (v, t, Misc.sort_and_compact (ras ++ kras))

*)

(**************************************************************)
(********************** Pretty Printing ***********************)
(**************************************************************)

let print_refineatom ppf = function
  | Conc p       -> F.fprintf ppf "%a" P.print p
  | Kvar (su, k) -> F.fprintf ppf "%a%a" Sy.print k Su.print su

let print_ras so ppf ras = 
  match so with 
  | None   -> F.fprintf ppf "%a" (Misc.pprint_many false ";" print_refineatom) ras
  | Some s -> ras |> Misc.flap (preds_of_refa s) |> A.pAnd
                  |> F.fprintf ppf "%a" P.print 

(* API *)
let print_reft_pred so ppf = function
  | (v,_,[])  -> F.fprintf ppf "@[{%a | true }@]" Sy.print v
  | (v,_,ras) -> F.fprintf ppf "@[{%a | @[%a@]}@]" Sy.print v (print_ras so) ras

(* API *)
let print_reft so ppf (v, t, ras) =
  F.fprintf ppf "@[{%a : %a | [%a]}@]" 
    Sy.print v
    Ast.Sort.print t
    (print_ras so) ras

(* API *)
let print_binding so ppf (x, r) = 
  F.fprintf ppf "@[%a:%a@]" Sy.print x (print_reft so) r 

(* API *)
let print_env so ppf env = 
  bindings_of_env env 
  |> F.fprintf ppf "@[%a@]" (Misc.pprint_many_box ";" (print_binding so))




let pprint_id ppf = function
  | Some id     -> F.fprintf ppf "id %d" id
  | None        -> F.fprintf ppf ""


let string_of_intlist = (String.concat ";") <.> (List.map string_of_int)

(* API *)
let print_tag ppf = function
  | [],_ -> F.fprintf ppf ""
  | is,s -> F.fprintf ppf "tag [%s] //%s" (string_of_intlist is) s 

(* API *)
let print_dep ppf = function
  | Adp ((t,_), (t',_)) -> F.fprintf ppf "add_dep: [%s] -> [%s]" (string_of_intlist t) (string_of_intlist t')
  | Ddp ((t,_), (t',_)) -> F.fprintf ppf "del_dep: [%s] -> [%s]" (string_of_intlist t) (string_of_intlist t')
  | Ddp_s (t,_)     -> F.fprintf ppf "del_dep: [%s] -> *" (string_of_intlist t) 
  | Ddp_t (t',_)    -> F.fprintf ppf "del_dep: * -> [%s]" (string_of_intlist t')

(* API *)
let print_wf so ppf (env, r, io, _) =
  F.fprintf ppf "wf: env @[[%a]@] @\n reft %a @\n %a @\n"
    (print_env so) env
    (print_reft so) r
    pprint_id io


let print_t so ppf {full=env;nontriv=nenv;guard=g;lhs=r1;rhs=r2;ido=io;tag=is} =
  let env = if !Constants.print_nontriv then nenv else env in 
  F.fprintf ppf 
  "constraint:@. env  @[[%a]@] @\n grd @[%a@] @\n lhs @[%a@] @\n rhs @[%a@] @\n %a %a @\n"
    (print_env so) env 
    P.print g
    (print_reft so) r1
    (print_reft so) r2
    pprint_id io
    print_tag is

(* API *)
let to_string         = Misc.fsprintf (print_t None)
let refa_to_string    = Misc.fsprintf print_refineatom 
let reft_to_string    = Misc.fsprintf (print_reft None)
let binding_to_string = Misc.fsprintf (print_binding None) 


 
(***************************************************************)
(*********************** Getter/Setter *************************)
(***************************************************************)

let theta_ra (su': Su.t) = function
  | Conc p       -> Conc (A.substs_pred p su')
  | Kvar (su, k) -> Kvar (Su.concat su su', k) 

(* API *)
let make_reft     = fun v so ras -> (v, so, List.map (theta_ra Su.empty) ras)
let vv_of_reft    = fst3
let sort_of_reft  = snd3
let ras_of_reft   = thd3
let shape_of_reft = fun (v, so, _) -> (v, so, [])
let theta         = fun subs (v, so, ras) -> (v, so, Misc.map (theta_ra subs) ras)

(* API *)
let env_of_t    = fun t -> t.full 
let grd_of_t    = fun t -> t.guard 
let lhs_of_t    = fun t -> t.lhs 
let rhs_of_t    = fun t -> t.rhs
let tag_of_t    = fun t -> t.tag
let ido_of_t    = fun t -> t.ido
let id_of_t     = fun t -> match t.ido with Some i -> i | _ -> assertf "C.id_of_t"
let make_t      = fun env p r1 r2 io is -> 
                    { full    = env ; 
                      nontriv = non_trivial env; 
                      guard   = A.simplify_pred p; 
                      lhs     = r1; 
                      rhs     = r2; 
                      ido     = io;
                      tag     = is }


let reft_of_sort so = make_reft (Sy.value_variable so) so []

let add_consts_env consts env = 
  consts 
  |> List.map (Misc.app_snd reft_of_sort) 
  |> List.fold_left (fun env (x,r) -> SM.add x r env) env

(* API *)
let add_consts_wf consts (env,x,y,z) = (add_consts_env consts env, x, y, z)

(* API *)
let add_consts_t consts t = {t with full = add_consts_env consts t.full}

(* API *)
let make_wf          = fun env r io -> (env, r, io, fun _ -> true)
let make_filtered_wf = fun env r io fltr -> (env, r, io, fltr)
let env_of_wf        = fst4
let reft_of_wf       = snd4
let id_of_wf         = function (_,_,Some i,_) -> i | _ -> assertf "C.id_of_wf"
let filter_of_wf     = fth4


(* API *)
let matches_deps ds = 
  let tt   = H.create 37 in
  let s_tt = H.create 37 in
  let t_tt = H.create 37 in
  List.iter begin function  
    | Adp (t, t') 
    | Ddp (t, t') -> H.add tt (t,t') ()
    | Ddp_s t     -> H.add s_tt t  ()
    | Ddp_t t'    -> H.add t_tt t' ()
  end ds;
  (fun (t, t') -> H.mem tt (t, t') || H.mem s_tt t || H.mem t_tt t')

(* API *)
let pol_of_dep = function Adp (_,_) -> true | _ -> false

(* API *)
let tags_of_dep = function 
  | Adp (t, t') | Ddp (t, t') -> t,t' 
  | _ -> assertf "tags_of_dep"

(* API *)
let make_dep b xo yo =
  match (b, xo, yo) with
  | true , Some t, Some t' -> Adp (t, t')
  | false, Some t, Some t' -> Ddp (t, t')
  | false, Some t, None    -> Ddp_s t
  | false, None  , Some t' -> Ddp_t t'
  | _                      -> assertf "FixConstraint.make_dep: match failure"

(* API *)
let preds_kvars_of_reft reft =
  List.fold_left begin fun (ps, ks) -> function 
    | Conc p -> p :: ps, ks
    | Kvar (xes, kvar) -> ps, (xes, kvar) :: ks 
  end ([], []) (ras_of_reft reft)


(***************************************************************)
(************* Add Distinct Ids to Constraints *****************)
(***************************************************************)

let max_id n cs =
  cs |> Misc.map_partial ido_of_t 
     >> (fun ids -> asserts (Misc.distinct ids) "Duplicate Ids")
     |> List.fold_left max n

(* API *)
let add_ids n cs =
  Misc.mapfold begin fun j c -> match c with
    | {ido = None} -> j+1, {c with ido = Some j}
    | c            -> j, c
  end ((max_id n cs) + 1) cs
