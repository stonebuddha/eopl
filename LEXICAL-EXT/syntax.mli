type program =
  | AProgram of top_level list

and top_level =
  | ExpTop of expression
  | ValTop of string * expression

and expression =
  | ConstExp of int * Ploc.t
  | DiffExp of expression * expression * Ploc.t
  | IsZeroExp of expression * Ploc.t
  | IfExp of expression * expression * expression * Ploc.t
  | VarExp of string * Ploc.t
  | LetExp of (string * expression) list * expression * Ploc.t
  | ProcExp of string list * expression * Ploc.t
  | CallExp of expression * expression list * Ploc.t
  | CondExp of (expression * expression) list * Ploc.t
  | LetrecExp of (string * string list * expression) list * expression * Ploc.t

val parse : char Stream.t -> program

type nameless_program =
  | NLAProgram of nameless_top_level list

and nameless_top_level =
  | NLExpTop of nameless_expression
  | NLValTop of string * nameless_expression

and nameless_expression =
  | NLConstExp of int * Ploc.t
  | NLDiffExp of nameless_expression * nameless_expression * Ploc.t
  | NLIsZeroExp of nameless_expression * Ploc.t
  | NLIfExp of nameless_expression * nameless_expression * nameless_expression * Ploc.t
  | NLVarExp of (int * int) * Ploc.t
  | NLLetExp of nameless_expression list * nameless_expression * Ploc.t
  | NLProcExp of nameless_expression * Ploc.t
  | NLCallExp of nameless_expression * nameless_expression list * Ploc.t
  | NLCondExp of (nameless_expression * nameless_expression) list * Ploc.t
  | NLLetrecExp of nameless_expression list * nameless_expression * Ploc.t
  | NLLetrecVarExp of (int * int) * Ploc.t
