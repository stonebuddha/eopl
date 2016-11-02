open Syntax

type refer = int

and store = expval list

and environment = refer list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ProcVal of proc

and proc = int * expression * environment ref

let string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ProcVal _ -> "<proc>"

let empty_env () = []

let extend_env refer env = refer :: env

let apply_env env var = List.nth env var

let default_store_size = 1024 * 1024

let empty_store () = (ref 0, ref (Array.make 0 (NumVal 0)))

let init_store (next, st) =
  let () = next := 0 in
  let () = st := Array.make default_store_size (NumVal 0) in
  ()

let newref eval (next, st) =
  if (!next) < default_store_size then
    let refer = !next in
    let () = next := refer + 1 in
    let () = (!st).(refer) <- eval in
    refer
  else
    raise Not_found

let deref refer (_, st) = (!st).(refer)

let setref refer eval (_, st) = (!st).(refer) <- eval

let the_store = empty_store ()

exception Interpreter_error of string * Ploc.t

type continuation =
  | EndCont
  | DiffFstCont of expression * environment * continuation * Ploc.t
  | DiffSndCont of expval * continuation * Ploc.t
  | IsZeroCont of continuation * Ploc.t
  | IfCont of expression * expression * environment * continuation * Ploc.t
  | LetCont of expval list * expression list * expression * environment * continuation * Ploc.t
  | CallRatorCont of expression list * environment * continuation * Ploc.t
  | CallRandCont of expval list * expression list * proc * environment * continuation * Ploc.t
  | AssignCont of refer * continuation * Ploc.t

let rec value_of_k exp env cont =
  match exp with
  | ConstExp (num, loc) -> apply_cont cont (NumVal num)
  | DiffExp (exp1, exp2, loc) ->
    value_of_k exp1 env (DiffFstCont (exp2, env, cont, loc))
  | IsZeroExp (exp1, loc) ->
    value_of_k exp1 env (IsZeroCont (cont, loc))
  | IfExp (exp1, exp2, exp3, loc) ->
    value_of_k exp1 env (IfCont (exp2, exp3, env, cont, loc))
  | VarExp (var, loc) -> apply_cont cont (deref (apply_env env var) the_store)
  | LetExp (exps, body, loc) ->
    (match exps with
     | [] -> value_of_k body env cont
     | exp1 :: exps' -> value_of_k exp1 env (LetCont ([], exps', body, env, cont, loc)))
  | ProcExp (arity, body, loc) -> apply_cont cont (ProcVal (arity, body, ref env))
  | CallExp (rator, rands, loc) ->
    value_of_k rator env (CallRatorCont (rands, env, cont, loc))
  | LetrecExp (p_bodies, letrec_body, loc) ->
    let saved_env = ref (empty_env ()) in
    let procs = List.map (fun (arity, p_body) -> ProcVal (arity, p_body, saved_env)) p_bodies in
    let env' = List.fold_left (fun env eval -> extend_env (newref eval the_store) env) env procs in
    let () = saved_env := env' in
    value_of_k letrec_body (!saved_env) cont
  | AssignExp (var, exp1, loc) ->
    value_of_k exp1 env (AssignCont (apply_env env var, cont, loc))

and apply_procedure_k proc arg_vals call_site cont =
  match proc with
  | (arity, body, saved_env) ->
    if arity = List.length arg_vals then
      value_of_k body (List.fold_left (fun env arg_val -> extend_env (newref arg_val the_store) env) (!saved_env) arg_vals) cont
    else
      raise (Interpreter_error ("the parameters and arguments are not consistent at call site", call_site))

and apply_cont cont eval =
  match cont with
  | EndCont -> eval
  | DiffFstCont (exp2, env, saved_cont, loc) ->
    value_of_k exp2 env (DiffSndCont (eval, saved_cont, loc))
  | DiffSndCont (eval1, saved_cont, loc) ->
    let eval2 = eval in
    (match (eval1, eval2) with
     | (NumVal num1, NumVal num2) -> apply_cont saved_cont (NumVal (num1 - num2))
     | _ -> raise (Interpreter_error ("the operands of diff should be numbers", loc)))
  | IsZeroCont (saved_cont, loc) ->
    let eval1 = eval in
    (match eval1 with
     | NumVal num1 -> apply_cont saved_cont (BoolVal (num1 = 0))
     | _ -> raise (Interpreter_error ("the operand of is_zero should be a number", loc)))
  | IfCont (exp2, exp3, env, saved_cont, loc) ->
    let eval1 = eval in
    (match eval1 with
     | BoolVal bool1 -> if bool1 then value_of_k exp2 env saved_cont else value_of_k exp3 env saved_cont
     | _ -> raise (Interpreter_error ("the predicate of if should be a boolean", loc)))
  | LetCont (evals, exps, body, env, saved_cont, loc) ->
    let eval1 = eval in
    let evals' = eval1 :: evals in
    (match exps with
     | [] ->
       let env' = List.fold_right (fun eval env -> extend_env (newref eval the_store) env) evals' env in
       value_of_k body env' saved_cont
     | exp1 :: exps' -> value_of_k exp1 env (LetCont (evals', exps', body, env, saved_cont, loc)))
  | CallRatorCont (rands, env, saved_cont, loc) ->
    let rator_val = eval in
    (match rator_val with
     | ProcVal proc ->
       (match rands with
        | [] -> apply_procedure_k proc [] loc saved_cont
        | rand :: rands' -> value_of_k rand env (CallRandCont ([], rands', proc, env, saved_cont, loc)))
     | _ -> raise (Interpreter_error ("the operator of call should be a procedure", loc)))
  | CallRandCont (arg_vals, rands, proc, env, saved_cont, loc) ->
    let rand_val = eval in
    let arg_vals' = rand_val :: arg_vals in
    (match rands with
     | [] -> apply_procedure_k proc (List.rev arg_vals') loc saved_cont
     | rand :: rands' -> value_of_k rand env (CallRandCont (arg_vals', rands', proc, env, saved_cont, loc)))
  | AssignCont (refer, saved_cont, loc) ->
    let eval1 = eval in
    let () = setref refer eval1 the_store in
    apply_cont saved_cont (NumVal 27)

let value_of_top_level top env =
  match top with
  | ValTop (var, exp1) ->
    let eval1 = value_of_k exp1 env EndCont in
    let () = print_endline ("val " ^ var ^ " = " ^ string_of_expval eval1 ^ ";") in
    extend_env (newref eval1 the_store) env
  | FunTop (p_name, arity, p_body) ->
    let saved_env = ref (empty_env ()) in
    let proc = ProcVal (arity, p_body, saved_env) in
    let () = saved_env := extend_env (newref proc the_store) env in
    let () = print_endline ("fun " ^ p_name ^ " is defined;") in
    !saved_env

let value_of_program (AProgram tops) =
  let () = init_store the_store in
  List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
