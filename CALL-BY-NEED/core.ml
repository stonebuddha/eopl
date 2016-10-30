open Syntax

type refer = int

and store = expval list

and environment = refer list

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

let extend_env refer env = refer :: env

let apply_env env var = List.nth env var

type stoval =
  | Evaled of expval
  | Thunk of expression * environment

let empty_store () = ref []

let init_store st = st := []

let newref sval st =
  let refer = List.length (!st) in
  let () = st := List.append (!st) [sval] in
  refer

let deref refer st = List.nth (!st) refer

let setref refer sval st =
  let rec inner refer st =
    if refer = 0 then
      sval :: List.tl st
    else
      List.hd st :: inner (refer - 1) (List.tl st) in
  st := inner refer (!st)

let the_store = empty_store ()

exception Interpreter_error of string * Ploc.t

let rec value_of exp env =
  match exp with
  | ConstExp (num, loc) -> NumVal num
  | DiffExp (exp1, exp2, loc) ->
    let eval1 = value_of exp1 env in
    let eval2 = value_of exp2 env in
    (match (eval1, eval2) with
     | (NumVal num1, NumVal num2) -> NumVal (num1 - num2)
     | _ -> raise (Interpreter_error ("the operands of diff should be numbers", loc)))
  | IsZeroExp (exp1, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | NumVal num1 -> BoolVal (num1 = 0)
     | _ -> raise (Interpreter_error ("the operand of is_zero should be a number", loc)))
  | IfExp (exp1, exp2, exp3, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | BoolVal bool1 -> if bool1 then value_of exp2 env else value_of exp3 env
     | _ -> raise (Interpreter_error ("the predicate of if should be a boolean", loc)))
  | VarExp (var, loc) ->
    let refer = apply_env env var in
    let sval = deref refer the_store in
    (match sval with
     | Evaled eval -> eval
     | Thunk (body, saved_env) ->
       let eval = value_of body saved_env in
       let () = setref refer (Evaled eval) the_store in
       eval)
  | LetExp (exps, body, loc) ->
    let evals = List.map (fun exp1 -> value_of exp1 env) exps in
    let env' = List.fold_left (fun env eval1 -> extend_env (newref (Evaled eval1) the_store) env) env evals in
    value_of body env'
  | ProcExp (body, loc) -> ProcVal (body, ref env)
  | CallExp (rator, rand, loc) ->
    let rator_val = value_of rator env in
    (match rator_val with
     | ProcVal proc -> let rand_ref = value_of_operand rand env in apply_procedure proc rand_ref
     | _ -> raise (Interpreter_error ("the operator of call should be a procedure", loc)))
  | LetrecExp (p_bodies, letrec_body, loc) ->
    let saved_env = ref (empty_env ()) in
    let procs = List.map (fun p_body -> ProcVal (p_body, saved_env)) p_bodies in
    let env' = List.fold_left (fun env eval -> extend_env (newref (Evaled eval) the_store) env) env procs in
    let () = saved_env := env' in
    value_of letrec_body !saved_env
  | BeginExp (exps, loc) ->
    let eval1 = value_of (List.hd exps) env in
    List.fold_left (fun _ exp1 -> value_of exp1 env) eval1 (List.tl exps)
  | AssignExp (var, exp1, loc) ->
    let refer = apply_env env var in
    let eval1 = value_of exp1 env in
    let () = setref refer (Evaled eval1) the_store in
    NumVal 27

and value_of_operand exp env =
  match exp with
  | VarExp (var, loc) -> apply_env env var
  | _ -> newref (Thunk (exp, env)) the_store

and apply_procedure proc arg_ref =
  match proc with
  | (body, saved_env) -> value_of body (extend_env arg_ref !saved_env)

let value_of_top_level top env =
  match top with
  | ValTop (var, exp1) ->
    let eval1 = value_of exp1 env in
    let () = print_endline ("val " ^ var ^ " = " ^ string_of_expval eval1 ^ ";") in
    extend_env (newref (Evaled eval1) the_store) env
  | FunTop (p_name, p_body) ->
    let saved_env = ref (empty_env ()) in
    let proc = ProcVal (p_body, saved_env) in
    let () = saved_env := extend_env (newref (Evaled proc) the_store) env in
    !saved_env

let value_of_program (AProgram tops) =
  let () = init_store the_store in
  List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
