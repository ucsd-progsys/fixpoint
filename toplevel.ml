module BS = BNstats
module SM = Ast.Symbol.SMap
module Co = Constants 
module C  = FixConstraint
module F  = Format
open Misc.Ops

(*****************************************************************)
(********************* Command line options **********************)
(*****************************************************************)

type t = { ts : Ast.Sort.t list
         ; ps : Ast.pred list
         ; cs : C.t list
         ; ws : C.wf list
         ; ds : C.dep list
         ; qs : Ast.Qualifier.t list
         ; s  : (Ast.Symbol.t * Ast.pred list) list}

let sift xs = 
  List.fold_left begin fun a -> function 
    | C.Srt t      -> {a with ts = t  :: a.ts }   
    | C.Axm p      -> {a with ps = p  :: a.ps } 
    | C.Cst c      -> {a with cs = c  :: a.cs }
    | C.Wfc w      -> {a with ws = w  :: a.ws } 
    | C.Dep d      -> {a with ds = d  :: a.ds }
    | C.Qul q      -> {a with qs = q  :: a.qs }
    | C.Sol (k,ps) -> {a with s  = (k,ps) :: a.s  }
  end {ts = []; ps = []; cs = []; ws = []; ds = []; qs = []; s = [] } xs

let parse f = 
  let _  = Errorline.startFile f in
  let ic = open_in f in
  let rv = Lexing.from_channel ic |> FixParse.defs FixLex.token in
  let _  = close_in ic in
  rv

let read_inputs usage = 
  print_now "\n \n \n \n \n";
  print_now "========================================================\n";
  print_now "© Copyright 2009 Regents of the University of California.\n";
  print_now "All Rights Reserved.\n";
  print_now "========================================================\n";
  print_now (Sys.argv |> Array.to_list |> String.concat " ");
  print_now "\n========================================================\n";
  let fs = ref [] in
  let _  = Arg.parse Co.arg_spec (fun s -> fs := s::!fs) usage in
  let fq = BS.time "parse" (Misc.flap parse) !fs |> sift in 
  (!fs, fq)
