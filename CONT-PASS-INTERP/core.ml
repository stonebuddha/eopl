open Syntax

type refer = int

and store = expval list

and environment = expval list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ProcVal of proc

and proc = expression * environment ref

let string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ProcVal _ -> "<proc>"

let empty_env () = []

let extend_env eval env = eval :: env

let apply_env env var = List.nth env var

exception Interpreter_error of string * Ploc.t

type continuation =
  | EndCont
  | DiffFstCont of expression * environment * continuation * Ploc.t
  | DiffSndCont of expval * continuation * Ploc.t
  | IsZeroCont of continuation * Ploc.t
  | IfCont of expression * expression * environment * continuation * Ploc.t
  | LetCont of expval list * expression list * expression * environment * continuation * Ploc.t
  | CallRatorCont of expression * environment * continuation * Ploc.t
  | CallRandCont of proc * continuation * Ploc.t

let rec value_of_k exp env cont =
  match exp with
  | ConstExp (num, loc) -> apply_cont cont (NumVal num)
  | DiffExp (exp1, exp2, loc) ->
    value_of_k exp1 env (DiffFstCont (exp2, env, cont, loc))
  | IsZeroExp (exp1, loc) ->
    value_of_k exp1 env (IsZeroCont (cont, loc))
  | IfExp (exp1, exp2, exp3, loc) ->
    value_of_k exp1 env (IfCont (exp2, exp3, env, cont, loc))
  | VarExp (var, loc) -> apply_cont cont (apply_env env var)
  | LetExp (exps, body, loc) ->
    (match exps with
     | [] -> value_of_k body env cont
     | exp1 :: exps' -> value_of_k exp1 env (LetCont ([], exps', body, env, cont, loc)))
  | ProcExp (body, loc) -> apply_cont cont (ProcVal (body, ref env))
  | CallExp (rator, rand, loc) ->
    value_of_k rator env (CallRatorCont (rand, env, cont, loc))
  | LetrecExp (p_bodies, letrec_body, loc) ->
    let saved_env = ref (empty_env ()) in
    let procs = List.map (fun p_body -> ProcVal (p_body, saved_env)) p_bodies in
    let env' = List.fold_left (fun env eval -> extend_env eval env) env procs in
    let () = saved_env := env' in
    value_of_k letrec_body (!saved_env) cont

and apply_procedure_k proc arg_val cont =
  match proc with
  | (body, saved_env) -> value_of_k body (extend_env arg_val !saved_env) cont

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
       let env' = List.fold_right extend_env evals' env in
       value_of_k body env' saved_cont
     | exp1 :: exps' -> value_of_k exp1 env (LetCont (evals', exps', body, env, saved_cont, loc)))
  | CallRatorCont (rand, env, saved_cont, loc) ->
    let rator_val = eval in
    (match rator_val with
     | ProcVal proc -> value_of_k rand env (CallRandCont (proc, saved_cont, loc))
     | _ -> raise (Interpreter_error ("the operator of call should be a procedure", loc)))
  | CallRandCont (proc, saved_cont, loc) ->
    let rand_val = eval in
    apply_procedure_k proc rand_val saved_cont

let value_of_top_level top env =
  match top with
  | ValTop (var, exp1) ->
    let eval1 = value_of_k exp1 env EndCont in
    let () = print_endline ("val " ^ var ^ " = " ^ string_of_expval eval1 ^ ";") in
    extend_env eval1 env
  | FunTop (p_name, p_body) ->
    let saved_env = ref (empty_env ()) in
    let proc = ProcVal (p_body, saved_env) in
    let () = saved_env := extend_env proc env in
    let () = print_endline ("fun " ^ p_name ^ " is defined;") in
    !saved_env

let value_of_program (AProgram tops) =
  List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
