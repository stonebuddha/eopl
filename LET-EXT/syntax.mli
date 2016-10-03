type program =
  | AProgram of top_level list

and top_level =
  | ExpTop of expression

and expression =
  | ConstExp of int * Ploc.t
  | DiffExp of expression * expression * Ploc.t
  | IsZeroExp of expression * Ploc.t
  | IfExp of expression * expression * expression * Ploc.t
  | VarExp of string * Ploc.t
  | LetExp of string * expression * expression * Ploc.t
  | MinusExp of expression * Ploc.t
  | AddExp of expression * expression * Ploc.t
  | MultExp of expression * expression * Ploc.t
  | QuotExp of expression * expression * Ploc.t
  | IsEqualExp of expression * expression * Ploc.t
  | IsGreaterExp of expression * expression * Ploc.t
  | IsLessExp of expression * expression * Ploc.t
  | ConsExp of expression * expression * Ploc.t
  | CarExp of expression * Ploc.t
  | CdrExp of expression * Ploc.t
  | IsNullExp of expression * Ploc.t
  | EmptylistExp of Ploc.t

val parse : char Stream.t -> program
