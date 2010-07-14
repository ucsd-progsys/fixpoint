
module F  = Format
module BS = BNstats
module Co = Constants 
module SM = Ast.Symbol.SMap
module H  = Ast.Horn
open Misc.Ops

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
  let _  = Errorline.startFile f in
  let ic = open_in f in
  let rv = Lexing.from_channel ic |> HornParse.horns HornLex.token in
  let _  = close_in ic in
  rv

let process f: H.t list =
  clean f;
  parse tmpname

let dump cs = 
  Format.printf "%a\n\n\n" (Misc.pprint_many true "\n" H.print) cs

let arities_of_ts (cs: H.t list) : int SM.t = failwith "TBD"

let interproc_of_ts (cs: H.t list) : string = failwith "TBD"

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
  !fs |> Misc.flap process |> dump 

let _ = main usage
