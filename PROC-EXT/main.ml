open Support
open Syntax
open Core

let main () =
  try Stream.of_channel (open_in Sys.argv.(1)) |> parse |> value_of_program
  with Invalid_argument msg -> print_endline "Usage: THIS filename"; exit 1
     | Sys_error msg -> print_endline msg; exit 1
     | Ploc.Exc (loc, Stream.Error msg) -> print_endline (string_of_loc loc ^ ": [bad syntax] " ^ msg); exit 1
     | Interpreter_error (msg, loc) -> print_endline (string_of_loc loc ^ ": [runtime error] " ^ msg); exit 1

let () = main ()
