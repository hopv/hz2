open Lexing
open Lexer

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg; None
  | Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let rec parse lexbuf =
  match parse_with_error lexbuf with
  | Some value -> value
  | None -> failwith "syntax error"

let read_from_flie filename =
  let ic = open_in filename in
  let rec read_loop acc =
    match input_line ic with
    | s -> s ^ "\n" ^ (read_loop acc) (* ;( *)
    | exception End_of_file -> acc 
  in read_loop ""

(* entry point *)
let () =
  let in_filename = ref "" in
  let out_filename = ref "" in
  let dhes = ref false in
  let dparsed = ref false in
  (* let trans_mode = ref "" in *)
  (* let not_mode = ref false in *)
  let set_str t s = t := s in
  let () = Arg.parse 
      [("-i", Arg.String (set_str in_filename), "input file");
       ("-o", Arg.String (set_str out_filename), "output file");
       ("-dhes", Arg.Unit (fun () -> dhes := true), "dump HES after reduction"); 
       ("-dparsed", Arg.Unit (fun () -> dparsed := true), "dump parsed tree"); 
       (* ("-may", Arg.Unit (fun () -> trans_mode := "may"), "may or must"); *)
       (* ("-must", Arg.Unit (fun () -> trans_mode := "must"), "may or must"); *)
       (* ("-path", Arg.Unit (fun () -> trans_mode := "path"), "path"); *)
       (* ("-not", Arg.Unit (fun () -> not_mode := true), "not?"); *)
      ]  print_endline "hz2 -i file [-o file]"
  in
  if !in_filename = "" then
    Printf.eprintf "Invalid arguments\n"
  else
    let filename_without_extension = Filename.remove_extension !in_filename in
    let filename_without_path = Filename.basename filename_without_extension in
    let out_filename = 
      if !out_filename = "" then Printf.sprintf "%s.v" filename_without_extension else !out_filename in
    let out_filename_tactics = Printf.sprintf "%s_tactics.v" filename_without_extension in
    let Horsz.Prog (_, e) as prog, apt =   
      !in_filename
      |> read_from_flie 
      |> Lexing.from_string
      |> parse in
    let () = if !dparsed then
        (Printf.eprintf "%s\n\n" @@ Horsz.string_of_prog prog;
         Printf.eprintf "%s\n" @@ Apt.string_of_apt apt) in
    let header =
      Printf.sprintf "%s\n\n%s" 
        (Horsz.string_of_prog prog) (Apt.string_of_apt apt) in
    let prog = Horsz_t.type_program prog in
    let hes = Trans.trans_program apt prog in
    (* let () = hes |> Hes.gen_used_funcs |> Util.(show_M show_S) |> print_endline in *)
    let hes = Hes.remove_unused_feq hes in
    let () = if !dhes then 
        Printf.eprintf "generated HES\n%s\n" @@ Hes.string_of_hes false hes in
    let hes = Hes.parametrize hes in
    let () = if !dhes then 
        Printf.eprintf "parametrized HES\n%s\n" @@ Hes.string_of_hes false hes in
    let section = Coq_gen.section_of_hes filename_without_path hes in
    (* let body = Coq.show_section section in *)
    let sec, ltacs = Coq.show_section_split section in
    let () = Printf.fprintf (open_out out_filename)
        "(*\n%s\n*)\n\n%s\nRequire Import HflTactics.\n%s" 
        header {|Add LoadPath "../".|} sec in
    Printf.fprintf (open_out out_filename_tactics) "%s" ltacs


