open Syntax

exception Interpreter_error of string * Ploc.t

val value_of_program : program -> unit
