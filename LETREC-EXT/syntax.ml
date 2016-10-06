type program =
  | AProgram of top_level list

and top_level =
  | ExpTop of expression
  | ValTop of string * expression
  | RecTop of string * string list * expression

and expression =
  | ConstExp of int * Ploc.t
  | DiffExp of expression * expression * Ploc.t
  | IsZeroExp of expression * Ploc.t
  | IfExp of expression * expression * expression * Ploc.t
  | VarExp of string * Ploc.t
  | LetExp of string * expression * expression * Ploc.t
  | ProcExp of string list * expression * Ploc.t
  | CallExp of expression * expression list * Ploc.t
  | LetrecExp of (string * string list * expression) list * expression * Ploc.t

let g = Grammar.gcreate (Plexer.gmake ())

let p = Grammar.Entry.create g "program"
let t = Grammar.Entry.create g "top level"
let e = Grammar.Entry.create g "expression"
let r = Grammar.Entry.create g "letrec binding"

let parse = Grammar.Entry.parse p

EXTEND
  p : [
    [ tops = LIST0 t -> AProgram tops ]
  ];
  t : [
    [ exp1 = e; ";" -> ExpTop exp1
    | "val"; var = LIDENT; "="; exp1 = e; ";" -> ValTop (var, exp1)
    | "fun"; p_name = LIDENT; "("; b_vars = LIST0 LIDENT SEP ","; ")"; "="; p_body = e; ";" -> RecTop (p_name, b_vars, p_body) ]
  ];
  e : [
    [ num = INT -> ConstExp (int_of_string num, loc)
    | "-"; "("; exp1 = e; ","; exp2 = e; ")" -> DiffExp (exp1, exp2, loc)
    | "is_zero"; "("; exp1 = e; ")" -> IsZeroExp (exp1, loc)
    | "if"; exp1 = e; "then"; exp2 = e; "else"; exp3 = e -> IfExp (exp1, exp2, exp3, loc)
    | var = LIDENT -> VarExp (var, loc)
    | "let"; var = LIDENT; "="; exp1 = e; "in"; body = e -> LetExp (var, exp1, body, loc)
    | "proc"; "("; vars = LIST0 LIDENT SEP ","; ")"; body = e -> ProcExp (vars, body, loc)
    | "("; rator = e; rands = LIST0 e; ")" -> CallExp (rator, rands, loc)
    | "letrec"; binds = LIST0 r; "in"; letrec_body = e -> LetrecExp (binds, letrec_body, loc) ]
  ];
  r : [
    [ p_name = LIDENT; "("; b_vars = LIST0 LIDENT SEP ","; ")"; "="; p_body = e -> (p_name, b_vars, p_body) ]
  ];
END
