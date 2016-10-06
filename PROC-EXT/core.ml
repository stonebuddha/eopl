open Syntax

type environment = (string * expval) list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ProcVal of proc

and proc = string list * expression * environment

let string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ProcVal _ -> "<proc>"

let empty_env () = []

let extend_env var eval env = (var, eval) :: env

let apply_env env var = List.assoc var env

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
    value_of body (extend_env var eval1 env)
  | ProcExp (vars, body, loc) -> ProcVal (vars, body, env)
  | CallExp (rator, rands, loc) ->
    let rator_val = value_of rator env in
    (match rator_val with
     | ProcVal proc -> let rand_vals = List.map (fun rand -> value_of rand env) rands in apply_procedure proc rand_vals loc
     | _ -> raise (Interpreter_error ("the operator of call shoud be a procedure", loc)))

and apply_procedure proc arg_vals loc =
  match proc with
  | (vars, body, saved_env) ->
    if List.length arg_vals = List.length vars then
      value_of body (List.fold_left (fun new_env (var, arg_val) -> extend_env var arg_val new_env) saved_env (List.combine vars arg_vals))
    else
      raise (Interpreter_error ("the parameters and arguments are not consistent at call site", loc))

let value_of_top_level (ExpTop exp1) =
  value_of exp1 (empty_env ()) |> string_of_expval |> print_endline

let value_of_program (AProgram tops) = List.iter value_of_top_level tops
