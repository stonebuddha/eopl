open Syntax

exception Interpreter_error of string * Ploc.t

val value_of_program : nameless_program -> unit
