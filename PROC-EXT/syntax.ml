open Support

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
  | ProcExp of string list * expression * bool * Ploc.t
  | CallExp of expression * expression list * Ploc.t

let rec free_variables exp =
  match exp with
  | ConstExp _ -> []
  | DiffExp (exp1, exp2, _) -> set_union (=) (free_variables exp1) (free_variables exp2)
  | IsZeroExp (exp1, _) -> free_variables exp1
  | IfExp (exp1, exp2, exp3, _) -> set_union (=) (set_union (=) (free_variables exp1) (free_variables exp2)) (free_variables exp3)
  | VarExp (var, _) -> [var]
  | LetExp (var, exp1, body, _) -> set_union (=) (free_variables exp1) (set_minus (=) (free_variables body) [var])
  | ProcExp (vars, body, _, _) -> set_minus (=) (free_variables body) vars
  | CallExp (rator, rands, _) -> List.fold_left (set_union (=)) (free_variables rator) (List.map free_variables rands)

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
    | "proc"; "("; vars = LIST0 LIDENT SEP ","; ")"; body = e -> ProcExp (vars, body, false, loc)
    | "("; rator = e; rands = LIST0 e; ")" -> CallExp (rator, rands, loc)
    | "traceproc"; "("; vars = LIST0 LIDENT SEP ","; ")"; body = e -> ProcExp (vars, body, true, loc) ]
  ];
END
