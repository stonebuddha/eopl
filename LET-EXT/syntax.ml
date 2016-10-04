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
  | LetExp of string * expression * expression * Ploc.t
  | EmptylistExp of Ploc.t
  | ListExp of expression list * Ploc.t
  | CondExp of (expression * expression) list * Ploc.t

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

let g = Grammar.gcreate (Plexer.gmake ())

let p = Grammar.Entry.create g "program"
let t = Grammar.Entry.create g "top level"
let e = Grammar.Entry.create g "expression"
let c = Grammar.Entry.create g "conditional clause"
let b = Grammar.Entry.create g "binary operator"
let u = Grammar.Entry.create g "unary operator"

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
    | bop = b; "("; exp1 = e; ","; exp2 = e; ")" -> BopExp (bop, exp1, exp2, loc)
    | uop = u; "("; exp1 = e; ")" -> UopExp (uop, exp1, loc)
    | "if"; exp1 = e; "then"; exp2 = e; "else"; exp3 = e -> IfExp (exp1, exp2, exp3, loc)
    | var = LIDENT -> VarExp (var, loc)
    | "let"; var = LIDENT; "="; exp1 = e; "in"; body = e -> LetExp (var, exp1, body, loc)
    | "emptylist" -> EmptylistExp loc
    | "list"; "("; exps = LIST0 e SEP ","; ")" -> ListExp (exps, loc)
    | "cond"; clauses = LIST0 c; "end" -> CondExp (clauses, loc) ]
  ];
  c : [
    [ exp1 = e; "==>"; exp2 = e -> (exp1, exp2) ]
  ];
  b : [
    [ "-" -> Diff
    | "+" -> Add
    | "*" -> Mult
    | "quot" -> Quot
    | "is_equal" -> IsEqual
    | "is_greater" -> IsGreater
    | "is_less" -> IsLess
    | "cons" -> Cons ]
  ];
  u : [
    [ "is_zero" -> IsZero
    | "minus" -> Minus
    | "car" -> Car
    | "cdr" -> Cdr
    | "is_null" -> IsNull ]
  ];
END
