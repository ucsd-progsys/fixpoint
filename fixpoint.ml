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
 *
 *)


(** read a set of constraints, solve, and dump out the solution *)

module BS = BNstats
module SM = Ast.Symbol.SMap
module Co = Constants 
module C  = FixConstraint
module S  = Solve
module F  = Format
module T  = Toplevel
module Sn = FixSolution

open Misc.Ops


let get_arity = function
  | []   -> assertf "Fixpoint: NO CONSTRAINTS!"
  | c::_ -> c |> C.tag_of_t |> fst |> List.length

(*****************************************************************)
(********************* Hooking into Solver ***********************)
(*****************************************************************)

let solve ac  = 
  let _       = print_now "Fixpoint: Creating  CI\n" in
  let a       = get_arity ac.C.cs in
  let ctx,s   = BS.time "create" (S.create ac.C.ts SM.empty ac.C.ps a ac.C.ds ac.C.cs ac.C.ws ac.C.s) ac.C.qs in
  let _       = print_now "Fixpoint: Solving \n" in
  let s, cs'  = BS.time "solve" (S.solve ctx) s in
  let _       = print_now "Fixpoint: Saving Result \n" in
  let _       = BS.time "save" (S.save !Co.save_file ctx) s in
  let _       = F.printf "%a \nUnsat Constraints:\n %a" 
                  Sn.print s 
                  (Misc.pprint_many true "\n" (C.print_t None)) cs' in
  cs'

let dump_solve cs = 
  let cs' = BS.time "solve" solve cs in
  let _   = BNstats.print stdout "Fixpoint Solver Time \n" in
  match cs' with 
  | [] -> (F.printf "\nSAT\n" ; exit 0)
  | _  -> (F.printf "\nUNSAT\n" ; exit 1)

(*****************************************************************)
(********************* Generate Imp Program **********************)
(*****************************************************************)

let dump_imp a = 
  (List.map (fun c -> C.Cst c) a.C.cs ++ List.map (fun c -> C.Wfc c) a.C.ws)
  |> ToImp.mk_program
  |> F.fprintf F.std_formatter "%a" Imp.print_program_as_c 
  |> fun _ -> exit 1 

(*****************************************************************)
(***************** Generate Simplified Constraints ***************)
(*****************************************************************)

let simplify_ts x = 
  if !Co.dump_simp = "andrey" 
  then (x |> List.map Simplification.simplify_t 
          |> List.filter (not <.> Simplification.is_tauto_t)
          |> Simplification.simplify_ts)
  else FixSimplify.simplify_ts x

let dump_simp ac = 
  let a     = get_arity ac.C.cs in
  let cs    = simplify_ts ac.C.cs in
  let s0    = Sn.of_bindings ac.C.ts SM.empty ac.C.ps ac.C.s in
  let ctx,_ = BS.time "create" (S.create ac.C.ts SM.empty ac.C.ps a ac.C.ds cs ac.C.ws []) [] in
  let _     = BS.time "save" (S.save !Co.save_file ctx) s0 in
  exit 1

(*****************************************************************)
(*********************** Main ************************************)
(*****************************************************************)

let usage = "Usage: fixpoint.native <options> [source-files]\noptions are:"

let main () =
  let cs  = usage |> Toplevel.read_inputs |> snd in 
  if !Co.dump_imp then 
    dump_imp cs 
  else if !Co.dump_simp <> "" then 
    dump_simp cs
  else
    dump_solve cs 

let _ = main ()
