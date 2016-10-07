open Syntax

exception Translator_error of string * Ploc.t

val translation_of_program : program -> nameless_program
