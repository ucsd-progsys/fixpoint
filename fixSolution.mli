(* 
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


exception UnmappedKvar of Ast.Symbol.t

type t
type p 

type def = Ast.pred * (Ast.Qualifier.t * Ast.Subst.t)

val empty        : t 
val read         : t -> Ast.Symbol.t -> Ast.pred list
val p_read       : t -> Ast.Symbol.t -> (p * Ast.pred) list 
val p_update     : t -> Ast.Symbol.t list -> p list list -> (bool * t)
val p_imp        : t -> p -> p -> bool
val of_bindings  : Ast.Sort.t list 
                   -> Ast.Sort.t Ast.Symbol.SMap.t 
                   -> Ast.pred list 
                   -> (Ast.Symbol.t * def list) list 
                   -> t

val print        : Format.formatter -> t -> unit
val print_stats  : Format.formatter -> t -> unit
val print_raw    : Format.formatter -> t -> unit

val save         : string -> t -> unit
val dump_cluster : t -> unit
