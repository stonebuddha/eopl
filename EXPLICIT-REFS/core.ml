open Syntax

type refer = int

and store = expval list

and environment = expval list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ProcVal of proc
  | RefVal of refer

and proc = expression * environment ref

let string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ProcVal _ -> "<proc>"
  | RefVal _ -> "<ref>"

let empty_env () = []

let extend_env eval env = eval :: env

let apply_env env var = List.nth env var

let empty_store () = []

let init_store st = st := empty_store ()

let newref eval st =
  let refer = List.length (!st) in
  let () = st := List.append (!st) [eval] in
  refer

let deref refer st = List.nth (!st) refer

let setref refer eval st =
  let rec inner refer st =
    if refer = 0 then
      eval :: List.tl st
    else
      List.hd st :: inner (refer - 1) (List.tl st) in
  st := inner refer (!st)

let the_store = ref (empty_store ())

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
  | VarExp (var, loc) -> apply_env env var
  | LetExp (exps, body, loc) ->
    let evals = List.map (fun exp1 -> value_of exp1 env) exps in
    let env' = List.fold_left (fun env eval1 -> extend_env eval1 env) env evals in
    value_of body env'
  | ProcExp (body, loc) -> ProcVal (body, ref env)
  | CallExp (rator, rand, loc) ->
    let rator_val = value_of rator env in
    (match rator_val with
     | ProcVal proc -> let rand_val = value_of rand env in apply_procedure proc rand_val
     | _ -> raise (Interpreter_error ("the operator of call should be a procedure", loc)))
  | LetrecExp (p_bodies, letrec_body, loc) ->
    let saved_env = ref (empty_env ()) in
    let procs = List.map (fun p_body -> ProcVal (p_body, saved_env)) p_bodies in
    let env' = List.fold_left (fun env eval -> extend_env eval env) env procs in
    let () = saved_env := env' in
    value_of letrec_body !saved_env
  | NewrefExp (exp1, loc) ->
    let eval1 = value_of exp1 env in
    let refer1 = newref eval1 the_store in
    RefVal refer1
  | DerefExp (exp1, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | RefVal refer1 -> deref refer1 the_store
     | _ -> raise (Interpreter_error ("the operand of deref should be a reference", loc)))
  | SetrefExp (exp1, exp2, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | RefVal refer1 ->
       let eval2 = value_of exp2 env in
       let () = setref refer1 eval2 the_store in
       NumVal 23
     | _ -> raise (Interpreter_error ("the first operand of setref should be a reference", loc)))
  | BeginExp (exps, loc) ->
    let eval1 = value_of (List.hd exps) env in
    List.fold_left (fun _ exp1 -> value_of exp1 env) eval1 (List.tl exps)

and apply_procedure proc arg_val =
  match proc with
  | (body, saved_env) -> value_of body (extend_env arg_val !saved_env)

let value_of_top_level top env =
  match top with
  | ValTop (var, exp1) ->
    let eval1 = value_of exp1 env in
    let () = print_endline ("val " ^ var ^ " = " ^ string_of_expval eval1 ^ ";") in
    extend_env eval1 env
  | FunTop (p_name, p_body) ->
    let saved_env = ref (empty_env ()) in
    let proc = ProcVal (p_body, saved_env) in
    let () = saved_env := extend_env proc env in
    !saved_env

let value_of_program (AProgram tops) =
  List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
