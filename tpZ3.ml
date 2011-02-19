(*
 * Copyright © 2008 The Regents of the University of California. All rights reserved.
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

(* This file is part of the LiquidC Project *)

module Co = Constants
module BS = BNstats
module A  = Ast
module Sy = A.Symbol
module So = A.Sort
module SM = Sy.SMap
module P  = A.Predicate
module E  = A.Expression
open Misc.Ops

module Prover : ProverArch.PROVER = struct

let mydebug = false 

(********************************************************************************)
(********************************** Type Definitions ****************************)
(********************************************************************************)

type decl = Vbl of Sy.t | Fun of Sy.t * int | Barrier

type var_ast = Const of Z3.ast | Bound of int * So.t

type t = { 
  c             : Z3.context;
  tint          : Z3.sort;
  tbool         : Z3.sort;
  vart          : (decl, var_ast) Hashtbl.t;
  funt          : (decl, Z3.func_decl) Hashtbl.t;
  tydt          : (So.t, Z3.sort) Hashtbl.t;
  mutable vars  : decl list ;
  mutable count : int;
  mutable bnd   : int;
}

(*************************************************************************)
(************************** Pretty Printing ******************************)
(*************************************************************************)

let pprint_decl ppf = function
  | Vbl x 	-> Format.fprintf ppf "%a" Sy.print x 
  | Barrier 	-> Format.fprintf ppf "----@." 
  | Fun (s, i) 	-> Format.fprintf ppf "%a[%i]" Sy.print s i

let dump_ast_type me a = 
  Z3.get_sort me.c a  
  |> Z3.sort_to_string me.c  
  |> Format.printf "@[z3%s@]@."

let dump_ast me a =
  Z3.ast_to_string me.c a
  |> Format.printf "@[%s@]@." 

let dump_decls me =
  Format.printf "Vars: %a" (Misc.pprint_many true "," pprint_decl) me.vars       

(************************************************************************)
(***************************** Stats Counters  **************************)
(************************************************************************)

let nb_set  		= ref 0
let nb_push 		= ref 0
let nb_pop  		= ref 0
let nb_unsat		= ref 0
let nb_query 		= ref 0
let nb_unsatLHS         = ref 0

(************************************************************************)
(********************** Misc. Constants *********************************)
(************************************************************************)

(* let bofi_n = Sy.of_string "_BOFI" *)
(* let iofb_n = Sy.of_string "_IOFB" *)
let div_n  = Sy.of_string "_DIV"
let tag_n  = Sy.of_string "_TAG"

let axioms = []
(* THESE CAUSE Z3 to SEG-FAULT (tests/t6.fq), 
 * most likely an error in the forall-translation
  let x = Sy.of_string "x" in
  [A.pForall ([(x, So.Bool)],                            
               A.pIff ((A.pAtom (A.eApp (iofb_n, [A.eVar x]), A.Eq, A.one)),
                       (A.pBexp (A.eVar x))));
   A.pForall ([(x, So.Int)],
               A.pIff (A.pBexp (A.eApp (bofi_n, [A.eVar x])),
                       A.pAtom (A.eVar x, A.Eq, A.one)))]
 *)

(* TBD these are related to ML and should be in DSOLVE, not here *)
let builtins = 
  SM.empty 
  |> SM.add tag_n  (So.t_func 0 [So.t_obj; So.t_int])
  |> SM.add div_n  (So.t_func 0 [So.t_int; So.t_int; So.t_int]) 
(*|> SM.add iofb_n (So.Func (0, [So.Bool; So.Int])) *)
(*|> SM.add bofi_n (So.Func (0, [So.Int; So.Bool])) *)

let select_t = So.t_func 0 [So.t_int; So.t_int]

let mk_select, is_select =
  let ss = "SELECT" in
  (fun f -> Sy.to_string f |> (^) (ss ^ "_") |> Sy.of_string),
  (fun s -> Sy.to_string s |> Misc.is_prefix ss)

let fresh = 
  let x = ref 0 in
  fun v -> incr x; (v^(string_of_int !x))

(*************************************************************************)
(********************** Typing *******************************************)
(*************************************************************************)

let varSort env s =
  try SM.find s env with Not_found -> 
    failure "ERROR: varSort cannot type %s in TPZ3 \n" (Sy.to_string s) 

let funSort env s =
  try SM.find s builtins with Not_found -> 
    try SM.find s env with Not_found -> 
      if is_select s then select_t else 
        failure "ERROR: could not type function %s in TPZ3 \n" (Sy.to_string s) 

let z3VarType me t =
  Misc.do_memo me.tydt begin fun t -> 
    if So.is_bool t 
    then me.tbool 
    else me.tint
  end t t
    
(***********************************************************************)
(********************** Identifiers ************************************)
(***********************************************************************)

let z3Var_memo me env x =
  Misc.do_memo me.vart
    (fun () -> 
      let t   = varSort env x |> z3VarType me in
      let sym = fresh "z3v" |> Z3.mk_string_symbol me.c in
      let rv  = Const (Z3.mk_const me.c sym t) in
      let _   = me.vars <- (Vbl x) :: me.vars in 
      rv) 
    () (Vbl x)

let z3Var me env x =
  match BS.time "z3Var memo" (z3Var_memo me env) x with
  | Const v     -> v
  | Bound (b,t) -> Z3.mk_bound me.c (me.bnd - b) (z3VarType me t)

let z3Bind me x t =
  me.bnd <- me.bnd + 1; 
  Hashtbl.replace me.vart (Vbl x) (Bound (me.bnd, t)); 
  me.vars <- (Vbl x) :: me.vars;
  Z3.mk_string_symbol me.c (fresh "z3b")

let z3Fun me env p t k = 
  Misc.do_memo me.funt begin fun _ -> 
    match So.func_of_t t with
    | None          -> assertf "MATCH ERROR: z3ArgTypes" 
    | Some (ts, rt) ->
        let ts = List.map (z3VarType me) ts in
        let rt = z3VarType me rt in
        let cf = Z3.mk_string_symbol me.c (fresh "z3f") in
        let rv = Z3.mk_func_decl me.c cf (Array.of_list ts) rt in
        let _  = me.vars <- (Fun (p,k))::me.vars in
        rv
  end () (Fun (p, k))

(************************************************************************)
(********************** Pred/Expr Transl ********************************)
(************************************************************************)

let is_z3_bool me a =
  a |> Z3.get_sort me.c   
    |> Z3.sort_to_string me.c
    |> (=) "bool"
 
let is_z3_int me a =
  a |> Z3.get_sort me.c   
    |> Z3.sort_to_string me.c
    |> (=) "int"

(* 
let z3Relf = function
  | A.Eq -> Z3.mk_eq
  | A.Gt -> Z3.mk_gt
  | A.Ge -> Z3.mk_ge
  | A.Lt -> Z3.mk_lt
  | A.Le -> Z3.mk_le
  | _    -> failure "MATCH FAILURE: TPZ3.z3Rel"
*)

(* TBD: casting int -> bool etc. nonsense, shouldnt happen here 

let rec cast me env a = function 
  | ("bool", "int") -> z3App me env iofb_n [] [a]
  | ("int", "bool") -> z3App me env bofi_n [] [a]
  | _               -> failure "MATCH ERROR: TPZ3.cast" 
 
and z3Cast me env a t = 
  let (st, st') = (Z3.get_type me.c a, z3VarType me t) 
                  |> Misc.map_pair (ast_type_to_string me) in
  if st = st' then a else cast me env a (st, st')  
*)

let rec z3Rel me env (e1, r, e2) =
  if A.sortcheck_pred (varSort env) (A.pAtom (e1, r, e2)) then 
    let a1, a2 = Misc.map_pair (z3Exp me env) (e1, e2) in 
    match r with 
    | A.Eq -> Z3.mk_eq me.c a1 a2 
    | A.Ne -> Z3.mk_distinct me.c [|a1; a2|]
    | A.Gt -> Z3.mk_gt me.c a1 a2
    | A.Ge -> Z3.mk_ge me.c a1 a2
    | A.Lt -> Z3.mk_lt me.c a1 a2
    | A.Le -> Z3.mk_le me.c a1 a2
  else begin 
    SM.iter (fun s t -> Format.printf "@[%a :: %a@]@." Sy.print s So.print t) env;
    Format.printf "@[%a@]@.@." P.print (A.pAtom (e1, r, e2));
    assertf "ERROR: z3Rel type error"
  end

and z3App me env p zes =
  let t  = funSort env p in
  let cf = z3Fun me env p t (List.length zes) in
  Z3.mk_app me.c cf (Array.of_list zes)

and z3Exp me env = function
  | A.Con (A.Constant.Int i), _ -> 
      Z3.mk_int me.c i me.tint 
  | A.Var s, _ -> 
      z3Var me env s
  | A.App (f, es), _ -> 
      z3App me env f (List.map (z3Exp me env) es)
  | A.Bin (e1, A.Plus, e2), _ ->
      Z3.mk_add me.c (Array.map (z3Exp me env) [|e1; e2|])
  | A.Bin (e1, A.Minus, e2), _ ->
      Z3.mk_sub me.c (Array.map (z3Exp me env) [|e1; e2|])
  | A.Bin((A.Con (A.Constant.Int n1), _), A.Times, (A.Con (A.Constant.Int n2), _)),_ ->
      Z3.mk_int me.c (n1 * n2) me.tint
  | A.Bin (e1, A.Times, e2), _ ->
      Z3.mk_mul me.c (Array.map (z3Exp me env) [|e1; e2|])
  | A.Bin (e1, A.Div, e2), _ -> 
      z3App me env div_n (List.map (z3Exp me env) [e1;e2])  
  | A.Bin (e, A.Mod, (A.Con (A.Constant.Int i), _)), _ ->
      Z3.mk_mod me.c (z3Exp me env e) (Z3.mk_int me.c i me.tint)
  | A.Ite (e1, e2, e3), _ -> 
      Z3.mk_ite me.c (z3Pred me env e1) (z3Exp me env e2) (z3Exp me env e3)
  | A.Fld (f, e), _ -> 
      z3App me env (mk_select f) [z3Exp me env e] (** REQUIRES: disjoint field names *)
  | A.Cst (e, _), _ -> 
      z3Exp me env e
  | A.Bot, _ -> 
      assertf "z3Exp: Cannot Convert Bot!" 

and z3Pred me env = function
  | A.True, _ -> 
      Z3.mk_true me.c
  | A.False, _ ->
      Z3.mk_false me.c
  | A.Not p, _ -> 
      Z3.mk_not me.c (z3Pred me env p)
  | A.And ps, _ -> 
      Z3.mk_and me.c (Array.of_list (List.map (z3Pred me env) ps))
  | A.Or ps, _  -> 
      Z3.mk_or me.c (Array.of_list (List.map (z3Pred me env) ps))
  | A.Imp (p1, p2), _ -> 
      Z3.mk_implies me.c (z3Pred me env p1) (z3Pred me env p2)
  | A.Iff (p1, p2), _ ->
      Z3.mk_iff me.c (z3Pred me env p1) (z3Pred me env p2)
  | A.Atom (e1, r, e2), _ ->
      z3Rel me env (e1, r, e2)
  | A.Bexp e, _ -> 
      let a = z3Exp me env e in
      let _ = asserts (is_z3_bool me a) "Bexp is not bool!" in
      a
 | A.Forall (xts, p), _ -> 
      let (xs, ts) = List.split xts in
      let zargs    = Array.of_list (List.map2 (z3Bind me) xs ts) in
      let zts      = Array.of_list (List.map  (z3VarType me) ts) in 
      let rv       = Z3.mk_forall me.c 0 [||] zts zargs (z3Pred me env p) in
      let _        = me.bnd <- me.bnd - (List.length xs) in
      rv

let z3Pred me env p = BS.time "z3Pred" (z3Pred me env) p

(***************************************************************************)
(***************** Low Level Query Interface *******************************)
(***************************************************************************)

let unsat me =
  let _ = if mydebug then (Printf.printf "UNSAT 1 \n"; flush stdout) in
  let rv = (BS.time "Z3.check" Z3.check me.c) = Z3.L_FALSE in
  let _ = if mydebug then (Printf.printf "UNSAT 2 \n"; flush stdout) in
  let _  = if rv then ignore (nb_unsat += 1) in 
  rv

let assert_axiom me p =
  (* Co.bprintf mydebug "@[Pushing axiom %s@]@." (Z3.ast_to_string me.c p); *)
  BS.time "Z3 assert axiom" (Z3.assert_cnstr me.c) p;
  asserts (not(unsat me)) "ERROR: Axiom makes background theory inconsistent!"

let rec vpop (cs,s) =
  match s with 
  | [] -> (cs,s)
  | Barrier :: t -> (cs,t)
  | h :: t -> vpop (h::cs,t) 

let prep_preds me env ps =
  let ps = List.rev_map (z3Pred me env) ps in
  let _  = me.vars <- Barrier :: me.vars in
  let _  = Z3.push me.c in
  ps

let push me ps =
  let _ = nb_push += 1 in
  let _ = me.count <- me.count + 1 in
  let _  = BS.time "Z3.push" Z3.push me.c in
  List.iter (fun p -> BS.time "Z3.ass_cst" (Z3.assert_cnstr me.c) p) ps
    
let pop me =
  let _ = incr nb_pop in
  let _ = me.count <- me.count - 1 in
  BS.time "Z3.pop" (Z3.pop me.c) 1 

let valid me p =
  let _ = push me [(Z3.mk_not me.c p)] in
  let rv = Timeout.do_timeout !Constants.z3_timeout unsat me in
  let rv = match rv with Some x -> x
                       | None -> failwith
                       "UNRECOVERABLE FIXPOINT ERROR: Z3 TIMED OUT" in
  let _ = pop me in
  rv

let clean_decls me =
  let cs, vars' = vpop ([],me.vars) in
  let _         = me.vars <- vars'  in 
  List.iter begin function 
    | Barrier    -> failure "ERROR: TPZ3.clean_decls" 
    | Vbl _ as d -> Hashtbl.remove me.vart d 
    | Fun _ as d -> Hashtbl.remove me.funt d
  end cs

let set me env vv ps =
  Hashtbl.remove me.vart (Vbl vv); 
  ps |> prep_preds me env |> push me;
  (* unsat me *) false

let full_filter me env _ ps =
  ps 
  |> List.rev_map (fun (x, p) -> (x, p, z3Pred me env p)) 
  |> Misc.filter (thd3 <+> valid me)
  |> List.map (fst3 <+> Misc.single)

let min_filter me env p_imp ps =
  ps 
  |> List.rev_map (fun (x, p) -> (x, p, z3Pred me env p)) 
  |> Misc.cov_filter (fun x y -> BS.time "p_imp" (p_imp (fst3 x)) (fst3 y)) (thd3 <+> valid me)
  |> List.map (fun (x, xs) -> List.map fst3 (x::xs))

(* DEBUG
let ps_to_string xps = List.map snd xps |> Misc.fsprintf (Misc.pprint_many false "," P.print)

let min_filter me env f ps = 
  let ps'  = min_filter me env f ps in
  let ps'' = full_filter me env f ps in
  let _    = asserti (List.length ps' = List.length ps'') 
             "difference in filters:\n[ps' = %s]\n[ps'' = %s]\n\n" 
             (ps_to_string ps') (ps_to_string ps'') in
  ps'
*)

let filter me = 
  if !Constants.minquals then min_filter me else full_filter me


(************************************************************************)
(********************************* API **********************************)
(************************************************************************)

(* API *)
let create ts env ps =
  (* let _  = Co.bprintf mydebug "TP.create ps = %a \n" (Misc.pprint_many false "," P.print) ps in  *)
  let _  = asserts (ts = []) "ERROR: TPZ3.create non-empty sorts!" in
  let c  = Z3.mk_context_x [|("MODEL", "false"); 
                             ("MODEL_PARTIAL", "true")|] in
  let me = {c     = c; 
            tint  = Z3.mk_int_sort c; 
            tbool = Z3.mk_bool_sort c; 
            tydt  = Hashtbl.create 37; 
            vart  = Hashtbl.create 37; 
            funt  = Hashtbl.create 37; 
            vars  = []; count = 0; bnd = 0} in
  let _  = List.iter (z3Pred me env <+> assert_axiom me) (axioms ++ ps) in
  me

(* API *)
let set_filter (me: t) (env: So.t SM.t) (vv: Sy.t) ps p_imp qs =
  let _   = ignore(nb_set   += 1); ignore(nb_query += List.length qs) in
  let ps  = BS.time "fixdiv" (List.rev_map A.fixdiv) ps in
  match BS.time "TP set" (set me env vv) ps with 
  | true  -> 
    let _ = nb_unsatLHS += 1 in
    let _ = pop me in
    List.map (fst <+> Misc.single) qs 

  | false ->
     qs 
     |> List.rev_map   (Misc.app_snd A.fixdiv) 
     |> List.partition (snd <+> P.is_tauto)
     |> Misc.app_fst (List.map (fst <+> Misc.single))
     |> Misc.app_snd (BS.time "TP filter" (filter me env p_imp))
     >> (fun _ -> pop me; clean_decls me)
     |> Misc.uncurry (++) 

(* API *)
let print_stats ppf me =
  Format.fprintf ppf
    "TP stats: sets=%d, pushes=%d, pops=%d, unsats=%d, queries=%d, count=%d, unsatLHS=%d \n" 
    !nb_set !nb_push !nb_pop !nb_unsat !nb_query (List.length me.vars) !nb_unsatLHS

end
