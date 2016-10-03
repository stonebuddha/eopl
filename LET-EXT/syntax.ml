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

let g = Grammar.gcreate (Plexer.gmake ())

let p = Grammar.Entry.create g "program"
let t = Grammar.Entry.create g "top level"
let e = Grammar.Entry.create g "expression"

let parse = Grammar.Entry.parse p

EXTEND
  p : [
    [ tops = LIST0 t -> AProgram tops ]
  ];
  t : [
    [ exp1 = e; ";" -> ExpTop exp1 ]
  ];
  e : [
    [ num = INT -> ConstExp (int_of_string num, loc)
    | "-"; "("; exp1 = e; ","; exp2 = e; ")" -> DiffExp (exp1, exp2, loc)
    | "is_zero"; "("; exp1 = e; ")" -> IsZeroExp (exp1, loc)
    | "if"; exp1 = e; "then"; exp2 = e; "else"; exp3 = e -> IfExp (exp1, exp2, exp3, loc)
    | var = LIDENT -> VarExp (var, loc)
    | "let"; var = LIDENT; "="; exp1 = e; "in"; body = e -> LetExp (var, exp1, body, loc)
    | "minus"; "("; exp1 = e; ")" -> MinusExp (exp1, loc)
    | "+"; "("; exp1 = e; ","; exp2 = e; ")" -> AddExp (exp1, exp2, loc)
    | "*"; "("; exp1 = e; ","; exp2 = e; ")" -> MultExp (exp1, exp2, loc)
    | "quot"; "("; exp1 = e; ","; exp2 = e; ")" -> QuotExp (exp1, exp2, loc)
    | "is_equal"; "("; exp1 = e; ","; exp2 = e; ")" -> IsEqualExp (exp1, exp2, loc)
    | "is_greater"; "("; exp1 = e; ","; exp2 = e; ")" -> IsGreaterExp (exp1, exp2, loc)
    | "is_less"; "("; exp1 = e; ","; exp2 = e; ")" -> IsLessExp (exp1, exp2, loc)
    | "cons"; "("; exp1 = e; ","; exp2 = e; ")" -> ConsExp (exp1, exp2, loc)
    | "car"; "("; exp1 = e; ")" -> CarExp (exp1, loc)
    | "cdr"; "("; exp1 = e; ")" -> CdrExp (exp1, loc)
    | "is_null"; "("; exp1 = e; ")" -> IsNullExp (exp1, loc)
    | "emptylist" -> EmptylistExp loc ]
  ];
END
