
module F  = Format
module BS = BNstats
module Co = Constants 
module SM = Ast.Symbol.SMap
module H  = Ast.Horn
open Misc.Ops


(***************************************************************************)
(************************* Parse Horn Clauses ******************************)
(***************************************************************************)

let tmpname = "tmp"

let clean f : unit =
  Misc.map_lines_of_file f tmpname begin fun s ->
    if String.length s > 3 && String.sub s 0 3 = "hc(" then
        let ss = Misc.chop s ", " in
        match ss with
        | [s1; s2; _] -> Printf.sprintf "%s, %s).\n\n" s1 s2
        | ss          -> assertf "bad string: %s" (String.concat "####" ss)
    else ""
  end

let parse f : H.t list = 
  let _  = clean f in
  let _  = Errorline.startFile tmpname in
  let ic = open_in f in
  let rv = Lexing.from_channel ic |> HornParse.horns HornLex.token in
  let _  = close_in ic in
  rv

(****************************************************************************)
(******************* Preprocess HC to get global information ****************)
(****************************************************************************)

k -> arity
k -> local vars
k -> call vars

k(x1,x2,x3) = a1 := x1, a2 := x2, a3 := x3; k(a1, a2, a3)

let arities_of_ts (cs: H.t list) : int SM.t = failwith "TBD"


(****************************************************************************)
(******************* Preprocess HC to get global information ****************)
(****************************************************************************)

let tx_gd (

let tx_hd (h: H.pr) : string = failwith "TBD"

let tx_t (c: H.t) : string = failwith "TBD"

let tx_ts (k: string, cs: H.t list) : string = failwith "TBD"

let tx cs = 

1. gather arities of each k
2. cluster constraints by k
3. translate constraint list
        - translate guards
        - translate head

(***************************************************************************)
(***************************** Output Clauses ******************************)
(***************************************************************************)

let dump cs = 
  Format.printf "%a\n\n\n" (Misc.pprint_many true "\n" H.print) cs

let usage = "hornToInterproc.native filename.pl"

let main usage = 
  print_now "\n \n \n \n \n";
  print_now "========================================================\n";
  print_now "© Copyright 2009 Regents of the University of California.\n";
  print_now "All Rights Reserved.\n";
  print_now "========================================================\n";
  print_now (Sys.argv |> Array.to_list |> String.concat " ");
  print_now "\n========================================================\n";
  let fs = ref [] in
  let _  = Arg.parse Co.arg_spec (fun s -> fs := s::!fs) usage in
  !fs |> Misc.flap parse |> dump 

let _ = main usage
