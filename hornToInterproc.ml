
module F  = Format
module BS = BNstats
module Co = Constants 
module SM = Misc.StringMap 
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

type t = {
  aritym : int SM.t;            (* k -> arity *)
  bindm  : string list SM.t;    (* k -> local bindings *)
  argn   : int;                 (* max-fun-args across all ks *)
  cm     : H.t list SM.t;       (* k -> cs *)
}

let create (cs: H.t list) : t =
  let cm = cs |> Misc.kgroupby (fun ((k,_),_) -> k) 
              |> List.fold_left (fun cm (k,cs) -> SM.add k cs cm) SM.empty in
  let aritym = SM.map (function (_,xs)::_ -> List.length xs) cm in
  let bindm  = SM.map ((Misc.flap H.support) <+> Misc.sort_and_compact) cm in
  let argn   = SM.fold (fun _ a n -> max a n) aritym 0 in
  { aritym = aritym; bindm = bindm; argn = argn; cm = cm }

(****************************************************************************)
(**************************** Generic Sequencers ****************************)
(****************************************************************************)

let gen f sep xs =
  xs |> Misc.map f |> String.concat sep

let geni f sep xs = 
  xs |> Misc.mapi f |> String.concat sep

let defn x n =
  geni (fun i _ -> Printf.sprintf "%s%d : int" x i) ", " (Misc.range 0 n)

(****************************************************************************)
(********************************* Translation ******************************)
(****************************************************************************)

let tx_gd = function
  | H.C p       -> Printf.sprintf "    assume %s;" (Misc.fsprintf Ast.Predicate.print p)
  | H.K (k, xs) -> Printf.sprintf "    %s () = %s(%s);" 
                     (geni (Printf.sprintf "a%d = %s;") " " xs)
                     k
                     (geni (fun i _ -> Printf.sprintf "a%d" i) "," xs)

let tx_hd = function 
  | "error", _ -> "    fail;"
  | _, xs      -> Printf.sprintf "    assume %s;" 
                     (geni (fun i x -> Printf.sprintf " z%d == %s " i x) " and " xs)

let tx_t k (head, guards) : string =
  Printf.sprintf "%s\n%s" (gen tx_gd "\n" guards) (tx_hd head)

let tx_def me = function
  | "error" -> 
      ""
  | k -> 
      let n = try SM.find k me.aritym with Not_found -> assertf "fucked here" in
      Printf.sprintf "proc %s(%s) returns ()" k (defn "z" n) 

let tx_k me (k, cs) =  
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
  let me = create cs in
  me.cm 
  |> Misc.sm_to_list
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
