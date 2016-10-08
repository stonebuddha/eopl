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
  | LetExp of string * expression * expression * Ploc.t
  | ProcExp of string * expression * Ploc.t
  | CallExp of expression * expression * Ploc.t
  | CondExp of (expression * expression) list * Ploc.t
  | LetrecExp of string * string * expression * expression * Ploc.t

let g = Grammar.gcreate (Plexer.gmake ())

let p = Grammar.Entry.create g "program"
let t = Grammar.Entry.create g "top level"
let e = Grammar.Entry.create g "expression"
let c = Grammar.Entry.create g "clause"

let parse = Grammar.Entry.parse p

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
  | NLVarExp of int * Ploc.t
  | NLLetExp of nameless_expression * nameless_expression * Ploc.t
  | NLProcExp of nameless_expression * Ploc.t
  | NLCallExp of nameless_expression * nameless_expression * Ploc.t
  | NLCondExp of (nameless_expression * nameless_expression) list * Ploc.t
  | NLLetrecExp of nameless_expression * nameless_expression * Ploc.t
  | NLLetrecVarExp of int * Ploc.t

EXTEND
  p : [
    [ tops = LIST0 t -> AProgram tops ]
  ];
  t : [
    [ exp1 = e; ";" -> ExpTop exp1
    | "val"; var = LIDENT; "="; exp1 = e; ";" -> ValTop (var, exp1) ]
  ];
  e : [
    [ num = INT -> ConstExp (int_of_string num, loc)
    | "-"; "("; exp1 = e; ","; exp2 = e; ")" -> DiffExp (exp1, exp2, loc)
    | "is_zero"; "("; exp1 = e; ")" -> IsZeroExp (exp1, loc)
    | "if"; exp1 = e; "then"; exp2 = e; "else"; exp3 = e -> IfExp (exp1, exp2, exp3, loc)
    | var = LIDENT -> VarExp (var, loc)
    | "let"; var = LIDENT; "="; exp1 = e; "in"; body = e -> LetExp (var, exp1, body, loc)
    | "proc"; "("; var = LIDENT; ")"; body = e -> ProcExp (var, body, loc)
    | "("; rator = e; rand = e; ")" -> CallExp (rator, rand, loc)
    | "cond"; clauses = LIST0 c; "end" -> CondExp (clauses, loc)
    | "letrec"; p_name = LIDENT; "("; b_var = LIDENT; ")"; "="; p_body = e; "in"; letrec_body = e -> LetrecExp (p_name, b_var, p_body, letrec_body, loc) ]
  ];
  c : [
    [ exp1 = e; "==>"; exp2 = e -> (exp1, exp2) ]
  ];
END
