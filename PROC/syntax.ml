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
  | ProcExp of string * expression * Ploc.t
  | CallExp of expression * expression * Ploc.t

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
    | "proc"; "("; var = LIDENT; ")"; body = e -> ProcExp (var, body, loc)
    | "("; rator = e; rand = e; ")" -> CallExp (rator, rand, loc) ]
  ];
END
