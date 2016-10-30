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
  | NewrefExp of expression * Ploc.t
  | DerefExp of expression * Ploc.t
  | SetrefExp of expression * expression * Ploc.t
  | BeginExp of expression list * Ploc.t
  | ListExp of expression list * Ploc.t

let empty_ctx () = []

let extend_ctx var ctx = var :: ctx

let rec apply_ctx var ctx =
  match ctx with
  | [] -> raise Not_found
  | saved_var :: saved_ctx -> if var = saved_var then 0 else 1 + apply_ctx var saved_ctx

exception Parser_error of string * Ploc.t

let g = Grammar.gcreate (Plexer.gmake ())

let p = Grammar.Entry.create g "program"
let t = Grammar.Entry.create g "top level"
let e = Grammar.Entry.create g "expression"
let l = Grammar.Entry.create g "let binding"
let r = Grammar.Entry.create g "letrec binding"

let parse = Grammar.Entry.parse p

EXTEND
  p : [
    [ tops = LIST0 t ->
      let (tops, ctx) = List.fold_left (
          fun (tops, ctx) top ->
            let (top, ctx) = top ctx in
            (top :: tops, ctx)) ([], empty_ctx ()) tops in
      AProgram (List.rev tops) ]
  ];
  t : [
    [ exp1 = e; ";" -> fun ctx -> (ValTop ("it", exp1 ctx), extend_ctx "it" ctx)
    | "val"; var = LIDENT; "="; exp1 = e; ";" -> fun ctx -> (ValTop (var, exp1 ctx), extend_ctx var ctx)
    | "fun"; p_name = LIDENT; "(";  b_var = LIDENT; ")"; "="; p_body = e; ";" -> fun ctx -> (FunTop (p_name, p_body (extend_ctx b_var (extend_ctx p_name ctx))), extend_ctx p_name ctx) ]
  ];
  e : [
    [ num = INT -> fun ctx -> ConstExp (int_of_string num, loc)
    | "-"; "("; exp1 = e; ","; exp2 = e; ")" -> fun ctx -> DiffExp (exp1 ctx, exp2 ctx, loc)
    | "is_zero"; "("; exp1 = e; ")" -> fun ctx -> IsZeroExp (exp1 ctx, loc)
    | "if"; exp1 = e; "then"; exp2 = e; "else"; exp3 = e -> fun ctx -> IfExp (exp1 ctx, exp2 ctx, exp3 ctx, loc)
    | var = LIDENT -> fun ctx ->
        (try VarExp (apply_ctx var ctx, loc)
         with Not_found -> raise (Parser_error ("the variable " ^ var ^ " is unbound", loc)))
    | "let"; binds = LIST0 l; "in"; body = e -> fun ctx ->
        let (vars, exps) = List.split binds in
        let ctx' = List.fold_left (fun ctx var -> extend_ctx var ctx) ctx vars in
        LetExp (List.map (fun exp -> exp ctx) exps, body ctx', loc)
    | "proc"; "("; var = LIDENT; ")"; body = e -> fun ctx -> ProcExp (body (extend_ctx var ctx), loc)
    | "("; rator = e; rand = e; ")" -> fun ctx -> CallExp (rator ctx, rand ctx, loc)
    | "letrec"; binds = LIST0 r; "in"; letrec_body = e -> fun ctx ->
        let (p_names, binds) = List.split binds in
        let ctx' = List.fold_left (fun ctx var -> extend_ctx var ctx) ctx p_names in
        let p_bodies = List.map (fun (b_var, p_body) -> p_body (extend_ctx b_var ctx')) binds in
        LetrecExp (p_bodies, letrec_body ctx', loc)
    | "newref"; "("; exp1 = e; ")" -> fun ctx -> NewrefExp (exp1 ctx, loc)
    | "deref"; "("; exp1 = e; ")" -> fun ctx -> DerefExp (exp1 ctx, loc)
    | "setref"; "("; exp1 = e; ","; exp2 = e; ")" -> fun ctx -> SetrefExp (exp1 ctx, exp2 ctx, loc)
    | "begin"; exps = LIST1 e SEP ";"; "end" -> fun ctx -> BeginExp (List.map (fun exp -> exp ctx) exps, loc)
    | "list"; "("; exps = LIST0 e SEP ","; ")" -> fun ctx -> ListExp (List.map (fun exp -> exp ctx) exps, loc) ]
  ];
  l : [
    [ var = LIDENT; "="; exp1 = e -> (var, exp1) ]
  ];
  r : [
    [ p_name = LIDENT; "("; b_var = LIDENT; ")"; "="; p_body = e -> (p_name, (b_var, p_body)) ]
  ];
END
