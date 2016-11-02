type program =
  | AProgram of top_level list

and top_level =
  | ValTop of string * expression
  | FunTop of string * int * expression

and expression =
  | ConstExp of int * Ploc.t
  | DiffExp of expression * expression * Ploc.t
  | IsZeroExp of expression * Ploc.t
  | IfExp of expression * expression * expression * Ploc.t
  | VarExp of int * Ploc.t
  | LetExp of expression list * expression * Ploc.t
  | ProcExp of int * expression * Ploc.t
  | CallExp of expression * expression list * Ploc.t
  | LetrecExp of (int * expression) list * expression * Ploc.t
  | AssignExp of int * expression * Ploc.t

exception Parser_error of string * Ploc.t

val parse : char Stream.t -> program
