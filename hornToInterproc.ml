
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

(*
 k -> arity        = #formals
 k -> bindings     = #temps 
 k -> max-fun-args = #for wierd interproc reasons 
 k(x1,x2,x3) = a1 := x1, a2 := x2, a3 := x3; k(a1, a2, a3)
 *)

type t = {
  aritym : int SM.t;            (* k -> arity *)
  bindm  : string list SM.t;    (* k -> local bindings *)
  argn   : int                  (* max-fun-args across all ks *)
}

let create (cs: H.t list) : t = failwith "TBD"

(****************************************************************************)
(******************* Preprocess HC to get global information ****************)
(****************************************************************************)

let gen f sep xs =
  xs |> Misc.map f |> String.concat sep

let geni f sep xs = 
  xs |> Misc.mapi f |> String.concat sep

let defn x n =
  geni (fun i _ -> Printf.sprintf "%s%d : int") ", " (range 0 n)

let tx_gd = function
  | H.C p       -> Printf.sprintf "    assume %s;" (Misc.fsprintf Predicate.print p)
  | H.K (k, xs) -> Printf.sprintf "    %s () = %s(%s);" 
                     (geni (Printf.sprintf "a%d = %s;") " " xs)
                     (geni (fun i _ -> Printf.sprintf "a%d" i) "," xs)

let tx_hd = function 
  | "error", _ -> "    fail;"
  | k, xs      -> Printf.sprintf "    assume %s;" 
                     (geni (fun i x -> Printf.sprintf " z%d == %s " i x) " and ")

let tx_t k (head, guards) : string =
  Printf.sprintf "%s\n%s" (gen tx_gd "\n" guards) (tx_hd hd)

let tx_def me = function
  | "error" -> 
      ""
  | k -> 
      let n = try SM.find k me.aritym with Not_found -> assertf "fucked here" in
      Printf.sprintf "proc %s(%s) returns ()" k (defn "z" n) 

let funargs me = 

let tx_k me (k: string, cs: H.t list) : string = 
  Printf.sprintf 
"
%s
var %s, %s;
begin
  if brandom then
%s
  endif
end
" 
(tx_def me k) 
(defn "a" me.argn) 
(gen (Printf.sprintf "%s : int") ", " (SM.find k me.bindm)) 
(gen (tx_t me) "  else\n" cs)

let tx cs =
  let me  = create cs in
  cs |> Misc.kgroupby (fun ((k,_),_) -> k)
     |> List.map (tx_k me)
     |> String.concat "\n\n"

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
