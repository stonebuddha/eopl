type program =
  | AProgram of top_level list

and top_level =
  | ExpTop of expression

and expression =
  | ConstExp of int * Ploc.t
  | BopExp of bin_op * expression * expression * Ploc.t
  | UopExp of un_op * expression * Ploc.t
  | IfExp of expression * expression * expression * Ploc.t
  | VarExp of string * Ploc.t
  | LetExp of (string * expression) list * expression * Ploc.t
  | LetSeqExp of (string * expression) list * expression * Ploc.t
  | EmptylistExp of Ploc.t
  | ListExp of expression list * Ploc.t
  | CondExp of (expression * expression) list * Ploc.t
  | PrintExp of expression * Ploc.t

and bin_op =
  | Diff
  | Add
  | Mult
  | Quot
  | IsEqual
  | IsGreater
  | IsLess
  | Cons

and un_op =
  | IsZero
  | Minus
  | Car
  | Cdr
  | IsNull

val parse : char Stream.t -> program
