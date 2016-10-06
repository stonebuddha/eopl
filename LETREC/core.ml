open Syntax

type environment = bind list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ProcVal of proc

and proc = string * expression * environment

and bind =
  | ValBind of string * expval
  | RecBind of string * string * expression

let string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ProcVal _ -> "<proc>"

let empty_env () = []

let extend_env bind env = bind :: env

let rec apply_env env var =
  match env with
  | [] -> raise Not_found
  | ValBind (saved_var, saved_val) :: saved_env ->
    if var = saved_var then
      saved_val
    else
      apply_env saved_env var
  | RecBind (p_name, b_var, p_body) :: saved_env ->
    if var = p_name then
      ProcVal (b_var, p_body, env)
    else
      apply_env saved_env var

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
    (try apply_env env var
     with Not_found -> raise (Interpreter_error ("the variable " ^ var ^ " is not in the environment", loc)))
  | LetExp (var, exp1, body, loc) ->
    let eval1 = value_of exp1 env in
    value_of body (extend_env (ValBind (var, eval1)) env)
  | ProcExp (var, body, loc) -> ProcVal (var, body, env)
  | CallExp (rator, rand, loc) ->
    let rator_val = value_of rator env in
    (match rator_val with
     | ProcVal proc -> let rand_val = value_of rand env in apply_procedure proc rand_val
     | _ -> raise (Interpreter_error ("the operator of call shoud be a procedure", loc)))
  | LetrecExp (p_name, b_var, p_body, letrec_body, loc) ->
    value_of letrec_body (extend_env (RecBind (p_name, b_var, p_body)) env)

and apply_procedure proc arg_val =
  match proc with
  | (var, body, saved_env) -> value_of body (extend_env (ValBind (var, arg_val)) saved_env)

let value_of_top_level (ExpTop exp1) =
  value_of exp1 (empty_env ()) |> string_of_expval |> print_endline

let value_of_program (AProgram tops) = List.iter value_of_top_level tops