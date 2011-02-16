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

module F   = Format
module A   = Ast
module E   = A.Expression
module P   = A.Predicate

module Q   = A.Qualifier
module Sy  = A.Symbol
module Su  = A.Subst
module SM  = Sy.SMap
module BS  = BNstats
module TP  = TpNull.Prover
module Co  = Constants
module IIM = Misc.IntIntMap
open Misc.Ops

let mydebug = false 

exception UnmappedKvar of Sy.t

type def = Ast.pred * (Ast.Qualifier.t * Ast.Subst.t) option
type p   = Sy.t * def
type t   = { m    : def list SM.t
           ; qs   : Q.t list
           ; impm : bool Misc.IntIntMap.t;
             (* (t1,t2) \in impm iff 
                  q1 => q2 /\ 
                  t1 = tag_of_qual q1 /\ 
                  t2 = tag_of_qual q2 *)
           }

(*************************************************************)
(************* Constructing Initial Solution *****************)
(*************************************************************)

let tag_of_qual = snd <.> Q.pred_of_t

let map_of_bindings (bs : (Sy.t * def list) list) =
  List.fold_left (fun s (k, defs) -> SM.add k defs s) SM.empty bs 

let quals_of_bindings bs =
  bs |> Misc.flap snd
     |> Misc.map_partial snd 
     |> Misc.sort_and_compact


(************************************************************)
(***************** Build Implication Graph ******************)
(************************************************************)

let check_tp tp sm q qs = 
  let vv  = Q.vv_of_t q in
  let lps = [Q.pred_of_t q] in
  qs |> List.map (tag_of_qual <*> Q.pred_of_t)
     |> TP.set_filter tp sm vv lps (fun _ _ -> false) 

let cluster_quals = Misc.groupby Q.sort_of_t 

let update_impm_for_quals tp sm impm (qs : Q.t list) = 
  List.fold_left begin fun impm q ->
    let tag   = tag_of_qual q in 
    qs |> check_tp tp sm q 
       |> List.map (fun tag' -> (tag, tag')) 
       |> List.fold_left (fun impm k -> IIM.add k true impm) impm 
  end qs

let impm_of_quals ts sm ps qs =
  let tp = TP.create ts sm ps in
  qs |> cluster_quals 
     |> List.fold_left (update_impm_for_quals tp sm) IIM.empty

(************************************************************)
(*********************** Profile/Stats **********************)
(************************************************************)

(* API *)
let print ppf s =
  SM.iter begin fun k ps -> 
    F.fprintf ppf "solution: %a := [%a] \n"  
    Sy.print k (Misc.pprint_many false ";" P.print) ps
  end s.m

(* API *)
let print_stats ppf s =
  let (sum, max, min, bot) =   
    (SM.fold (fun _ qs x -> (+) x (List.length qs)) s.m 0,
     SM.fold (fun _ qs x -> max x (List.length qs)) s.m min_int,
     SM.fold (fun _ qs x -> min x (List.length qs)) s.m max_int,
     SM.fold (fun _ qs x -> x + (if List.exists P.is_contra qs then 1 else 0)) s.m 0) in
  let n   = Sy.sm_length s.m in
  let avg = (float_of_int sum) /. (float_of_int n) in
  F.fprintf ppf "# Vars: (Total=%d, False=%d) Quals: (Total=%d, Avg=%f, Max=%d, Min=%d)\n" 
    n bot sum avg max min

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
  s.m 
  |> Sy.sm_to_list 
  |> List.map snd 
  |> Misc.groupby key_of_quals
  |> List.map begin function 
     | [] -> assertf "impossible" 
     | (ps::_ as pss) -> Co.cprintf Co.ol_solve 
                         "SolnCluster: preds %d = size %d \n"
                         (List.length ps) (List.length pss)
     end
  |> ignore

(************************************************************)
(*************************** API ****************************)
(************************************************************)

(* API *)
let of_bindings ts sm ps (bs : (Sy.t * def list) list) =
  let m    = map_of_bindings bs in
  let qs   = quals_of_bindings bs in
  let impm = impm_of_quals ts sm ps qs in
  {m = m; qs = qs; impm = impm}

(* API *)
let empty = of_bindings [] SM.empty [] [] 

(* API *)
let p_read s k =
  let _ = asserts (SM.mem k s.m) "ERROR: p_read : unknown kvar %s\n" (Sy.to_string k) in
  s.m |> SM.find k |> List.map (fun d -> ((k,d), fst d)) 

(* API *)
let read s k = p_read s k |> List.map snd

(* API *)
let p_imp s p1 p2 = match p1, p2 with
  | (_, (p1, Some (q1,su1), (_, (p2, Some (q2, su2))) ->
      su1 = su2 &&  (Misc.map_pair tag_of_qual (q1, q2) |> IIM.mem s.impm) 
  | _ -> 
      false

(* INV: qs' \subseteq qs *)
let update m k ds' =
  let ds  = SM.find k m in
  (if mydebug then 
    ds |> List.filter (fun d -> not (List.mem d ds'))
       |> List.map fst
       |> F.printf "Dropping %a: (%d) %a \n" Sy.print k (List.length qs)
            (Misc.pprint_many false "," P.print)
  );
  (not (Misc.same_length ds ds'), SM.add k ds' m)


(* API *)
let p_update s0 ks kds =  
  let t  = H.create 17 in
  let _  = List.iter (fun (k, d) -> H.add t k d) kds in
  List.fold_left begin fun (b, m) k -> 
      let ds       = H.find_all t k in 
      let (b', m') = update m k ds in
      (b || b', m')
  end (false, s0) ks
  |> Misc.app_snd (fun m -> { s0 with m = m })  

(* {{{ DEPRECATED 

let read s k = 
  try SM.find k s.m with Not_found -> begin
    Printf.printf "ERROR: Solution.read : unknown kvar %s \n" 
    (Sy.to_string k);
    raise (UnmappedKvar k)
  end


let query s k =
  try SM.find k s with Not_found -> []

let add s k qs' = 
  let qs   = query s k in
  let qs'' = qs' ++ qs in
  (not (Misc.same_length qs qs''), SM.add k qs'' s)

let merge s1 s2 =
  SM.fold (fun k qs s -> add s k qs |> snd) s1 s2 

let map_of_bindings (bs : (Sy.t * def list) list) =
  bs |> List.map (fun (k, defs) -> (k, List.map fst defs)) 
     |> List.fold_left (fun s (k, ps) -> SM.add k ps s) SM.empty 
  
  }}} *)
