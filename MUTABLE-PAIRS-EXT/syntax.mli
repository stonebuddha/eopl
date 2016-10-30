type program =
  | AProgram of top_level list

and top_level =
  | ValTop of string * expression
  | FunTop of string * expression

and expression =
  | ConstExp of int * Ploc.t
  | DiffExp of expression * expression * Ploc.t
  | IsZeroExp of expression * Ploc.t
  | IfExp of expression * expression * expression * Ploc.t
  | VarExp of int * Ploc.t
  | LetExp of expression list * expression * Ploc.t
  | ProcExp of expression * Ploc.t
  | CallExp of expression * expression * Ploc.t
  | LetrecExp of expression list * expression * Ploc.t
  | BeginExp of expression list * Ploc.t
  | AssignExp of int * expression * Ploc.t
  | NewpairExp of expression * expression * Ploc.t
  | LeftExp of expression * Ploc.t
  | RightExp of expression * Ploc.t
  | SetleftExp of expression * expression * Ploc.t
  | SetrightExp of expression * expression * Ploc.t
  | NewarrayExp of expression * expression * Ploc.t
  | ArrayrefExp of expression * expression * Ploc.t
  | ArraysetExp of expression * expression * expression * Ploc.t
  | ArraylengthExp of expression * Ploc.t

exception Parser_error of string * Ploc.t

val parse : char Stream.t -> program
