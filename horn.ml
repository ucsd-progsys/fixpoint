
module H = Ast.Horn

let parse f : H.t list = 
  let _  = Errorline.startFile f in
  let ic = open_in f in
  let rv = Lexing.from_channel ic |> FixParse.horns FixLex.token in
  let _  = close_in ic in
  rv

let dump cs = 
  Format.printf "%a" (Misc.pprint_many true "\n" H.print) cs

let arities_of_ts (cs: t list) : int SM.t = failwith "TBD"

let interproc_of_ts (cs: t list) : string = failwith "TBD"

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
