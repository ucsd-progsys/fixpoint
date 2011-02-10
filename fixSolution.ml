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

 
(*************************************************************)
(******************** Solution Management ********************)
(*************************************************************)

module F  = Format
module H  = Hashtbl
module A  = Ast
module E  = A.Expression
module P  = A.Predicate

module Q  = A.Qualifier
module Sy = A.Symbol
module Su = A.Subst
module SM = Sy.SMap
module BS = BNstats

open Misc.Ops

let mydebug = false 

exception UnmappedKvar of Sy.t


type p = Sy.t * A.pred * (Q.t * Su.t) option 
(*
HEREHEREHERE
type t = { m  : A.pred list SM.t
         ; qs : Q.t list
         ; 
*)

(* API *)
let of_bindings = List.fold_left (fun s (k, ps) -> SM.add k ps s) SM.empty
let of_qbindings = assertf "TBD: of_qbindings"

(* API *)
let empty = of_bindings []

(* API *)
let query s k =
  try SM.find k s with Not_found -> []

(* API *)
let read s k = 
  try SM.find k s with Not_found -> begin
    Printf.printf "ERROR: Solution.read : unknown kvar %s \n" (Sy.to_string k);
    raise (UnmappedKvar k)
  end

(* INV: qs' \subseteq qs *)
let update s k qs' =
  let qs  = read s k in
  (if mydebug then 
    qs |> List.filter (fun q -> not (List.mem q qs')) 
       (* |> List.length *) 
       |> F.printf "Dropping %a: (%d) %a \n" Sy.print k (List.length qs) (Misc.pprint_many false "," P.print)
  );
  (not (Misc.same_length qs qs'), SM.add k qs' s)

let add s k qs' = 
  let qs   = query s k in
  let qs'' = qs' ++ qs in
  (not (Misc.same_length qs qs''), SM.add k qs'' s)

let merge s1 s2 =
  SM.fold (fun k qs s -> add s k qs |> snd) s1 s2 

(* API *)
let print ppf sm =
  SM.iter begin fun k ps -> 
    F.fprintf ppf "solution: %a := [%a] \n"  
    Sy.print k (Misc.pprint_many false ";" P.print) ps
  end sm

(* API *)
let print_stats ppf s = 
  let (sum, max, min, bot) =   
    (SM.fold (fun _ qs x -> (+) x (List.length qs)) s 0,
     SM.fold (fun _ qs x -> max x (List.length qs)) s min_int,
     SM.fold (fun _ qs x -> min x (List.length qs)) s max_int,
     SM.fold (fun _ qs x -> x + (if List.exists P.is_contra qs then 1 else 0)) s 0) in
  let avg = (float_of_int sum) /. (float_of_int (Sy.sm_length s)) in
  F.fprintf ppf "# Vars: (Total=%d, False=%d) Quals: (Total=%d, Avg=%f, Max=%d, Min=%d)\n" 
                (Sy.sm_length s) bot sum avg max min

(* API *)
let save fname s =
  let oc  = open_out fname in
  let ppf = F.formatter_of_out_channel oc in
  F.fprintf ppf "@[%a@] \n" print s;
  close_out oc

let key_of_quals qs = 
  qs |> List.map P.to_string 
     |> List.sort compare
     |> String.concat ","

(* API *)
let dump_cluster s = 
   s |> Sy.sm_to_list 
     |> List.map snd 
     |> Misc.groupby key_of_quals
     |> List.map begin function [] -> assertf "impossible" | (ps::_ as pss) -> 
          Constants.cprintf Constants.ol_solve "SolnCluster: preds %d = size %d \n"
            (List.length ps) (List.length pss)
        end
     |> ignore

(* API *)
let p_update s0 ks kqs = 
  let t  = H.create 17 in
  let _  = List.iter (fun (k, q) -> H.add t k q) kqs in
  List.fold_left begin fun (b, s) k -> 
      let qs       = H.find_all t k in 
      let (b', s') = update s k qs in
      (b || b', s')
  end (false, s0) ks

(* API *)
let p_read s k =
  read s k 
  |> List.map (fun p -> ((k, p), p))

(* API *)
let p_imp _ _ = failwith "TBD: fixSolution.p_imp"
