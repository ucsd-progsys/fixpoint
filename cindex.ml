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

(***************************************************************)
(**** This module implements constraint indexing ***************)
(***************************************************************)
module H  = Hashtbl
module F  = Format
module BS = BNstats
module Co = Constants
module C  = FixConstraint
module IM = Misc.IntMap
module IS = Misc.IntSet
module SM = Ast.Symbol.SMap 
module SS = Ast.Symbol.SSet
module P  = Ast.Predicate

open Misc.Ops

(***********************************************************************)
(***************** Index Data Structures and Accessors *****************)
(***********************************************************************)

type rank = {
  id    : C.id;
  scc   : int;
  simpl : bool;
  tag   : C.tag;
}

let string_of_tag t = 
  Printf.sprintf "[%s]" (Misc.map_to_string string_of_int t)

let pprint_rank ppf r = 
  Format.fprintf ppf "id=%d, scc=%d, tag=%a" 
    r.id r.scc C.print_tag r.tag

module WH = 
  Heaps.Functional(struct 
      type t = int * rank 
      let compare (ts,r) (ts',r') = 
        if r.scc <> r'.scc then compare r.scc r'.scc else
          if ts <> ts' then - (compare ts ts') else 
            if !Constants.ptag && r.tag <> r'.tag then compare r.tag r'.tag else
              compare r.simpl r'.simpl
    end)

type wkl = WH.t

type t = 
  { cnst  : FixConstraint.t IM.t     (* id   -> refinement_constraint *) 
  ; rnkm  : rank IM.t                (* id   -> dependency rank *)
  ; depm  : C.id list IM.t           (* id   -> successor ids *)
  ; pend  : (C.id, unit) H.t         (* id   -> is in wkl ? *)
  ; rts   : IS.t                     (* {rank} members are "root" sccs *)
  ; ds    : C.dep list               (* add/del dep list *)
  ; rdeps : (int * int) list         (* real dependencies *)  
  }

let get_ref_rank me c =
  Misc.do_catch "ERROR: Cindex.get_ref_rank" (IM.find (C.id_of_t c)) me.rnkm

let get_ref_constraint me i = 
  Misc.do_catch "ERROR: Cindex.get_ref_constraint" (IM.find i) me.cnst

(***********************************************************************)
(******************** Building Real Dependencies ***********************)
(***********************************************************************)

let refa_ko = function C.Kvar (_,k) -> Some k | _ -> None

let reft_ks = function (_,_,ras) -> Misc.map_partial refa_ko ras

let lhs_ks c = 
  c |> C.lhs_of_t
    |> reft_ks 
    |> SM.fold (fun _ (r:C.reft) l -> (reft_ks r) ++ l) (C.env_of_t c)

let rhs_ks c =
  c |> C.rhs_of_t |> reft_ks 

let make_deps cm = 
  let get = fun km k -> try SM.find k km with Not_found -> [] in
  let upd = fun id km k -> SM.add k (id::(get km k)) km in
  let km  = IM.fold (fun id c vm -> List.fold_left (upd id) vm (lhs_ks c)) cm SM.empty in
  IM.fold begin fun id c acc ->
    List.fold_left begin fun (dm, deps) k -> 
      let kds = get km k in
      let deps' = List.map (fun id' -> (id, id')) kds in
      (IM.add id kds dm, (deps' ++ deps)) 
    end acc (rhs_ks c) 
  end cm (IM.empty,[])

(***********************************************************************)
(************* Adjusting Dependencies with Provided Tag-Deps ***********)
(***********************************************************************)

let delete_deps cm dds = 
  let delf = C.matches_deps dds in
  let tagf = fun x -> IM.find x cm |> C.tag_of_t in
  List.filter (not <.> delf <.> Misc.map_pair tagf)
  
let add_deps cm ads ijs = 
  let tt = H.create 37 in
  let _  = IM.iter (fun id c -> H.add tt (C.tag_of_t c) id) cm in
  ads |> Misc.map C.tags_of_dep
      |> Misc.map (Misc.map_pair (H.find_all tt))
      |> Misc.flap (Misc.uncurry Misc.cross_product)
      |> (++) ijs

let adjust_deps cm ds = 
  let ads, dds = List.partition C.pol_of_dep ds in
  !Constants.adjdeps <?> (add_deps cm ads <.> delete_deps cm dds)

(***********************************************************************)
(**************************** Dependency SCCs **************************)
(***********************************************************************)

let string_of_cid cm id = 
  try 
    IM.find id cm 
    |> C.tag_of_t
    |> Misc.fsprintf C.print_tag
    |> Printf.sprintf "%d: %s" id 
  with _ -> assertf "string_of_cid: impossible" 

let make_rankm cm ranks = 
  ranks
    |>: (fun (id, r) -> 
          let c = IM.find id cm in
          id, { id    = id
              ; scc   = r
              ; simpl = (not !Co.psimple) || (C.is_simple c)
              ; tag   = C.tag_of_t c})
    |> IM.of_list
    
(*
  List.fold_left begin fun rm (id, r) -> 
    let c = IM.find id cm in
    IM.add id {id    = id; 
               scc   = r; 
               simpl = (not !Co.psimple) || (C.is_simple c); 
               tag   = C.tag_of_t c;} rm
  end IM.empty ranks 
*)

let make_roots rankm ijs =
  let sccs = rankm |> IM.to_list |> Misc.map (fun (_,r) -> r.scc) in 
  let sccm = List.fold_left (fun is scc -> IS.add scc is) IS.empty sccs in
  List.fold_left begin fun sccm (i,j) ->
    let ir = (IM.find i rankm).scc in
    let jr = (IM.find j rankm).scc in
    if ir <> jr then IS.remove jr sccm else sccm
  end sccm ijs

let is_rhs_conc = 
  C.rhs_of_t <+>
  C.ras_of_reft <+> 
  List.exists (function C.Conc p -> not (P.is_tauto p) | _ -> false)

let im_findall i im = try IM.find i im with Not_found -> []

let is_addall im is = List.fold_left (IS.add |> Misc.flip) im is

(* A constraint c is non-live if its rhs is a k variable that is not
 * (transitively) read. 
 * roots := { c | (rhs_of_t c) has a concrete predicate }
 * lives := PRE*(roots) where Pre* is refl-trans-clos of the depends-on relation *)

let make_lives cm real_deps =
  let dm = List.fold_left (fun im (i, j) -> IM.add j (i :: (im_findall j im)) im) IM.empty real_deps in
  let js = IM.fold (fun i c roots -> if is_rhs_conc c then i::roots else roots) cm [] in
  let js = is_addall IS.empty js in
  (js, IS.empty)
  |> Misc.fixpoint begin fun (js, vm) ->
       let vm = IS.fold (fun j vm -> IS.add j vm) js vm in
       let js =
         IS.fold begin fun j js ->
              im_findall j dm |> List.filter (fun j -> not (IS.mem j vm)) |> is_addall js
         end js IS.empty
       in ((js, vm), js != IS.empty)
     end
  |> (fst <+> snd) 
  >> (IS.cardinal <+> Printf.printf "#Live Constraints: %d \n") 

let create_raw ds cm dm real_deps =
  let deps = adjust_deps cm ds real_deps in
  let rnkm = deps |> Fcommon.scc_rank "constraint" (string_of_cid cm) (IM.domain cm)
                  |> make_rankm cm in
  { cnst = cm; ds  = ds; rdeps = real_deps; rnkm  = rnkm
  ; depm = dm; rts = make_roots rnkm deps;  pend = H.create 17}


(***********************************************************************)
(**************************** API **************************************)
(***********************************************************************)

(* API *) 
let print ppf me =
  List.iter (Format.fprintf ppf "@[%a@] \n" C.print_dep) me.ds; 
  IM.iter (fun _ c -> Format.fprintf ppf "@[%a@] \n" (C.print_t None) c) me.cnst
 
let save fname me = 
  Misc.with_out_file fname begin fun oc -> 
    let ppf = F.formatter_of_out_channel oc in 
    F.fprintf ppf "//Sliced Constraints@.";
    F.fprintf ppf "@[%a@] \n" print me
  end


(* The "adjusted" dependencies are used to create the SCC ranks ONLY.
 * For soundness, the "real" dependencies must be used to push 
 * "successors" into the worklist. *)

(* API *)
let create ds cs =
  let cm            = cs |>: (Misc.pad_fst C.id_of_t) |> IM.of_list in 
  let dm, real_deps = make_deps cm in
  create_raw ds cm dm real_deps 

(* API *)
let slice me = 
  let lives = make_lives me.cnst me.rdeps in
  let cm    = me.cnst  
              |> IM.filter (fun i _ -> IS.mem i lives) in
  let dm    = me.depm  
              |> IM.filter (fun i _ -> IS.mem i lives) 
              |> IM.map (List.filter (fun j -> IS.mem j lives)) in
  let rdeps = me.rdeps 
              |> Misc.filter (fun (i,j) -> IS.mem i lives && IS.mem j lives) in
  
  create_raw me.ds cm dm rdeps
  >> save !Co.save_file

(* API *) 
let slice_wf me ws = 
  let ks = me.cnst 
           |> IM.range 
           |> Misc.flap C.kvars_of_t 
           |> Misc.map snd 
           |> SS.of_list 
  in Misc.filter (C.reft_of_wf <+> C.kvars_of_reft <+> List.exists (fun (_,k) -> SS.mem k ks)) ws
  
  

(* API *) 
let deps me c =
  (try IM.find (C.id_of_t c) me.depm with Not_found -> [])
  |> List.map (get_ref_constraint me)

(* API *)
let to_list me = IM.range me.cnst

(* 
(* API *)
let to_live_list me =
  me.cnst |> IM.to_list 
          |> Misc.map_partial (fun (i,c) -> if IS.mem i me.livs then Some c else None)

*)

let sort_iter_ref_constraints me f = 
  me.rnkm |> IM.to_list
          |> List.sort (fun (_,r) (_,r') -> compare r.tag r'.tag) 
          |> List.iter (fun (id,_) -> f (IM.find id me.cnst)) 

(* API *)
let wpush =
  let timestamp = ref 0 in
  fun me w cs ->
    incr timestamp;
    List.fold_left 
      (fun w c -> 
        let id = C.id_of_t c in
        if Hashtbl.mem me.pend id then w else 
          (Co.cprintf Co.ol_solve "Pushing %d at %d \n" id !timestamp; 
           Hashtbl.replace me.pend id (); 
           WH.add (!timestamp, get_ref_rank me c) w))
      w cs

let wstring w = 
  WH.fold (fun (_,r) acc -> r.id :: acc) w [] 
  |> List.sort compare
  |> Misc.map_to_string string_of_int

(* API *)
let wpop me w =
  try 
    let _, r = WH.maximum w in
    let _    = Hashtbl.remove me.pend r.id in
    let c    = get_ref_constraint me r.id in
    let _    = Co.cprintf Co.ol_solve "popping (%a) "pprint_rank r in
    let _    = Co.cprintf Co.ol_solve "from wkl = %s \n" (wstring w) in 
    (Some c, WH.remove w)
  with Heaps.EmptyHeap -> (None, w) 

let roots me =
  IM.fold begin fun id r sccm ->
   (*  if not (IM.mem r.scc me.rts) then sccm else *)
      let rs = try IM.find r.scc sccm with Not_found -> [] in
      IM.add r.scc (r::rs) sccm
  end me.rnkm IM.empty
  |> IM.map (List.hd <.> List.sort compare)
  |> IM.to_list
  |> Misc.map (fun (_,r) -> get_ref_constraint me r.id) 

(* API *)
let winit me = 
  roots me |> wpush me WH.empty  

 
(* iter (Format.fprintf ppf "@[%a@.@]" (C.print_t None)) me; *)
  (* if !Co.dump_ref_constraints then begin
    Format.fprintf ppf "Refinement Constraints: \n";
    iter (Format.fprintf ppf "@[%a@.@]" (C.print_t None)) me;
    Format.fprintf ppf "\n SCC Ranked Refinement Constraints: \n";
    sort_iter_ref_constraints me (Format.fprintf ppf "@[%a@.@]" (C.print_t None)); 
  end *)
