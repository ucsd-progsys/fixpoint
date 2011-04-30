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

(* Theorem Prover API *)

module type PROVER = 
sig
  type t 
 
  val create      : Ast.Sort.t list                         (* sorts        *) 
                    -> Ast.Sort.t Ast.Symbol.SMap.t         (* environment  *)
                    -> Ast.pred list                        (* axioms       *) 
                    -> Ast.Symbol.t list                    (* distinct constants, sorts in env *)
                    -> t
 
  val set_filter  : t 
                    -> Ast.Sort.t Ast.Symbol.SMap.t 
                    -> Ast.Symbol.t 
                    -> Ast.pred list 
                    -> ('a -> 'a -> bool)
                    -> ('a * Ast.pred) list 
                    -> 'a list list
                       
  val print_stats : Format.formatter -> t -> unit

end
