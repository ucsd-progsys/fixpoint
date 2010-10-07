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

open Misc.Ops

module A = Ast
module P = Ast.Predicate
module Sy = A.Symbol
module So = A.Sort
module TP = TpZ3.Prover
 
(***************************************************************)
(************************** Refinement *************************)
(***************************************************************)

module ImpGraph = Map.Make(struct
                            type t = A.pred
                            let compare = compare
                          end)
module IM = ImpGraph

type t = A.pred list IM.t

let filter_tp tpc sm p ps =
  TP.set_filter tpc sm (Sy.from_string "VV") So.t_obj [p] (List.map snd qs)

  (* API *)
let build_implication_graph (tpc: TP.t) (sm: So.t SM.t) (ps: A.pred list) = 
  List.fold_left (fun im p -> IM.add p (filter_tp tpc sm p ps) im) IM.empty ps

  (* API *)
let check_implication (im: t) (p1: A.pred) (p2: A.pred) =
  if IM.mem p1 then
    List.mem p2 (IM.find p1)
  else
    false

  (* API *)
let compute_avg_degree (im: t) =
  IM.fold (fun st ps -> (fst st + List.length ps, snd st + 1)) t (0, 0)
