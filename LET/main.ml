open Syntax
open Core

let string_of_loc loc =
  let fp = Ploc.first_pos loc in
  let lp = Ploc.last_pos loc in
  let ln = Ploc.line_nb loc in
  let lnl = Ploc.line_nb_last loc in
  let bp = Ploc.bol_pos loc in
  let bpl = Ploc.bol_pos_last loc in
  string_of_int ln ^ "-" ^ string_of_int lnl ^ ":" ^ string_of_int (fp - bp + 1) ^ "-" ^ string_of_int (lp - bpl)

let main () =
  try Stream.of_channel (open_in Sys.argv.(1)) |> parse |> value_of_program
  with Invalid_argument msg -> print_endline "Usage: THIS filename"; exit 1
     | Sys_error msg -> print_endline msg; exit 1
     | Ploc.Exc (loc, Stream.Error msg) -> print_endline (string_of_loc loc ^ ": [bad syntax] " ^ msg); exit 1
     | Interpreter_error (msg, loc) -> print_endline (string_of_loc loc ^ ": [runtime error] " ^ msg); exit 1

let () = main ()
