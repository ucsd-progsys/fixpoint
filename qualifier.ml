(*
 * Copyright © 2009-11 The Regents of the University of California. 
 * All rights reserved. 
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
 * This module implements a module for representing and manipulating Qualifiers.
 * *)

module F = Format

module P  = Ast.Predicate
module E  = Ast.Expression
module Sy = Ast.Symbol
module So = Ast.Sort
module Su = Ast.Subst
module SM = Sy.SMap
module IM = Misc.IntMap
open Misc.Ops
open Ast
(**************************************************************************)
(***************************** Qualifiers *********************************)
(**************************************************************************)
  
type t = { name    : Sy.t 
         ; vvar    : Sy.t
         ; vsort   : So.t
         ; params  : (Sy.t * So.t) list
         ; pred    : pred
         ; args    : expr list option 
           (* when args = Some es, es = vv'::[e1;...;en]
              where vv' is the applied vv and e1...en are the args applied to ~A1,...,~An *)
         }

let rename      = fun n -> fun q -> {q with name = n} 
let name_of_t   = fun q -> q.name
let vv_of_t     = fun q -> q.vvar
let sort_of_t   = fun q -> q.vsort
let pred_of_t   = fun q -> q.pred
let params_of_t = fun q -> q.params

let args_of_t q  =
  let xs = q.vvar :: List.map fst q.params in
  let es = match q.args with
           | Some es -> es
           | None    -> List.map eVar xs
  in Misc.combine "Qualifier.args_of_t" xs es


let print_param ppf (x, t) =
  F.fprintf ppf "%a:%a" Sy.print x So.print t 

let print_params ppf args =
  F.fprintf ppf "%a" (Misc.pprint_many false ", " print_param) args

let print ppf q = 
  F.fprintf ppf "qualif %a(%a):%a" 
    Sy.print q.name
    print_params q.params 
    P.print q.pred

let print_short ppf q = 
  F.fprintf ppf "(%a):%a" 
    (Misc.pprint_many false ", " So.print) (List.map snd q.params)
    P.print q.pred

let print_args ppf q =
  q |> args_of_t |> List.map snd 
    |> F.fprintf ppf "%a(%a)" Sy.print q.name (Misc.pprint_many false ", " E.print) 
   
(**********************************************************************)
(****************** Canonizing Wildcards (e.g. _ ---> ~A) *************)
(**********************************************************************)

let is_free params x = Misc.list_assoc_maybe x params |> Misc.maybe_bool |> not
(* not (Sy.SMap.mem x params) *)


(* API *)
let canonizer params =
  let fresh = Misc.mk_string_factory "~A" |> fst |> (fun f -> f <+> Sy.of_string <+> eVar) in
  let memo  = Hashtbl.create 7 in
  function
    | (Var x, _) when is_free params x && Hashtbl.mem memo x -> 
        Hashtbl.find memo x
    | (Var x, _) when is_free params x && Sy.is_wild_fresh x ->
        fresh () 
    | (Var x, _) when is_free params x && Sy.is_wild_any x -> 
        fresh () >> Hashtbl.replace memo x
    | e -> e

(**************************************************************************)
(*************** Expanding Away Sets of Ops and Rels **********************)
(**************************************************************************)
 
let expand_with_list f g =
  List.map f <+> Misc.cross_flatten <+> Misc.map g

let expand_with_pair f g =
  Misc.map_pair f <+> Misc.uncurry Misc.cross_product <+> Misc.map g

let crunchExpr f e1s xs e2s =
  List.map begin fun e1 -> 
    List.map begin fun e2 ->
      List.map begin fun x ->
        f (e1, x, e2)
      end xs
    end e2s
  end e1s
  |> List.flatten |> List.flatten

let rec expand_p ((p,_) as pred) = match p with 
   | And ps             -> expand_ps pAnd ps
   | Or ps              -> expand_ps pOr ps
   | Not p              -> expand_p p |> List.map pNot 
   | Imp (p1,p2)        -> expand_pp pImp (p1, p2)
   | Iff (p1,p2)        -> expand_pp pIff (p1, p2)
   | Forall(qs, p)      -> expand_p p |> List.map (fun p -> pForall (qs, p))
   | Bexp e             -> expand_e e |> List.map pBexp
   | MAtom (e1, rs, e2) -> let (e1s, e2s) = Misc.map_pair expand_e (e1,e2) in
                           crunchExpr pAtom e1s rs e2s
   | Atom (e1, r, e2)   -> let (e1s, e2s) = Misc.map_pair expand_e (e1,e2) in
                           crunchExpr pAtom e1s [r] e2s
   | _                  -> [pred]

and expand_e ((e,_) as expr) = match e with
   | MExp es            -> Misc.flap expand_e es
   | App (f, es)        -> expand_es (fun es -> eApp (f, es)) es
   | Bin (e1, op, e2)   -> expand_ep (fun (e1,e2) -> eBin (e1, op, e2)) (e1, e2) 
   | MBin (e1, ops, e2) -> let e1s, e2s = Misc.map_pair expand_e (e1, e2) in
                           crunchExpr eBin e1s ops e2s
   | Fld (s, e)         -> expand_e e |> List.map (fun e -> eFld (s,e))
   | Cst (e, t)         -> expand_e e |> List.map (fun e -> eCst (e,t))
   | Ite (p,e1,e2)      -> let e1s, e2s = Misc.map_pair expand_e (e1, e2) in
                           let ps       = expand_p p in 
                           List.map begin fun e1 ->
                             List.map begin fun e2 ->
                               List.map begin fun p ->
                                 eIte (p, e1, e2)
                               end ps
                             end e2s
                           end e1s
                           |> List.flatten |> List.flatten
   | _ -> [expr]

and expand_ps x = expand_with_list expand_p x
and expand_pp x = expand_with_pair expand_p x
and expand_es x = expand_with_list expand_e x
and expand_ep x = expand_with_pair expand_e x

(* API *)
let expand_qual q = 
  expand_p q.pred
  |> List.map (fun p -> {q with pred = p})

(**************************************************************************)
(*************** Expanding Away Sets of Ops and Rels **********************)
(**************************************************************************)
 
(* make_def_deps : name -> [(name, [expr])] of calls within each qual *)
let make_def_deps q = 
  let res = ref [] in
  P.map begin fun p -> 
    p >> (function Bexp (App (f, args),_), _ -> res := (f, args) :: !res | _ -> ()) 
  end id q.pred
  >| (q.name, !res)

let check_def_deps qm = 
  List.iter begin fun (n, fargs) ->
      List.iter begin fun (f, args) ->
        match SM.finds f qm with
        | [q] -> asserts (List.length args = List.length q.params) 
                 "Malformed Qualifier: %s with incorrect application of %s"
                 (Sy.to_string n) (Sy.to_string f)
        | []  -> assertf "Malformed Qualifier: %s refers to unknown %s" 
                 (Sy.to_string n) (Sy.to_string f)
        | _   -> assertf "Malformed Qualifier: %s refers to multiply defined %s" 
                 (Sy.to_string n) (Sy.to_string f)
      end fargs
  end

let order_by_defs qm qs = 
  let is   = Misc.range 0 (List.length qs)                                      in
  let qis  = List.combine qs is                                                 in
  let i2q  = qis  |>: Misc.swap |> IM.of_list  |> Misc.flip IM.find             in
  let i2s  = i2q <+> name_of_t <+> Sy.to_string                                 in  
  let n2i  = qis  |>: Misc.app_fst name_of_t |> SM.of_list |> Misc.flip SM.find in
  let deps = qs |>: make_def_deps >> check_def_deps qm                          in
  let ijs  = deps |> Misc.flap (fun (n,fargs) -> fargs |>: (fun (f,_) -> (n, f)))   
                  |> List.map (Misc.map_pair n2i)                               in
  let irs  = Fcommon.scc_rank "qualifier-deps" i2s is ijs                       in 
  Misc.fsort snd irs 
  |>: (fst <+> i2q)

let expand_def qm = function
  | Bexp (App (f, args),_), _ 
   -> let fq = SM.find f qm in
      let _  = asserts (List.length args = List.length fq.params) in
      fq.params 
      |> List.map fst
      |> Misc.flip List.combine args
      |> Su.of_list
      |> substs_pred fq.pred
  | p -> p
    
(* this MUST precede any renaming as renaming can screw up name resolution *)
let compile_definitions qs = 
  let qm   = List.fold_left (fun qm q -> SM.adds q.name [q] qm) SM.empty qs in
  let qs'  = order_by_defs qm qs                                            in 
  List.fold_left begin fun qm q -> 
    let q' = {q with pred = P.map (expand_def qm) id q.pred } in
    SM.add q.name q' qm
  end SM.empty qs'
  |> SM.range

(**************************************************************************)
(************************* Normalize Qualifier Sets ***********************)
(**************************************************************************)
 
let remove_duplicates qs =
  qs |> Misc.kgroupby (Misc.fsprintf print_short)
     |> List.map (fun (_,x::_) -> x)

let rename_qual q i = 
  {q with name = Sy.suffix q.name (string_of_int i)}

let uniquely_rename qs =
  Misc.mapfold begin fun m q ->
    if SM.mem q.name m then
      let i = SM.find q.name m in
      (SM.add q.name (i+1) m, rename_qual q i)
    else 
      (SM.add q.name 0 m, q)
  end SM.empty qs 
  |> snd

(* API *)
let normalize qs =
  qs |> Misc.flap expand_qual
     |> remove_duplicates
     (* |> compile_definitions *)
     |> uniquely_rename

(**************************************************************************)
(********************************** Create ********************************)
(**************************************************************************)
 
(* Rename to ensure unique names *)
let subst_vv v' q =
  { q with vvar = v' ; pred = P.subst q.pred q.vvar (eVar v')} 

let close_params vts p =
  p |> P.support
    |> List.filter (Sy.is_wild <&&> is_free vts) 
    |> List.map (fun x -> (x, So.t_int (* t_generic 0 causes blowup? *)))
    |> (@) vts (* Sy.SMap.of_list *)

let create n v t vts p =
  { name   = n 
  ; vvar   = v
  ; vsort  = t
  ; pred   = p
  ; params = close_params vts p 
  ; args   = None }

(* API *)
let create n v t vts p =
  create n v t vts p
  (* |> subst_vv (Sy.value_variable t) *) (* TODO: eliminate *)
  |> (fun q -> {q with pred = P.map id (canonizer q.params) q.pred })

(* API *)
let subst su q = 
  su (* |> Su.to_list *) 
     |> Ast.substs_pred q.pred
     |> create q.name (vv_of_t q) (sort_of_t q) (List.tl q.params)

(* API *)
let inst q es = match es with 
  | (Var v, _) :: _ ->
    let xs = q.vvar :: (List.map fst q.params)   in
    let p  = es |> Misc.combine "Qualifier.inst" xs 
                |> Su.of_list 
                |> Ast.substs_pred q.pred 
    in { q with vvar  = v; pred  = p ; args  = Some es }
  | _ -> assertf "Error: bad call to Qual.inst"


