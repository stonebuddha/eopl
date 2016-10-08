open Support
open Syntax

type environment = bind list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ProcVal of proc

and proc = nameless_expression * environment

and bind =
  | ValBind of expval

let string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ProcVal _ -> "<proc>"

exception Impossible

let empty_env () = []

let extend_env bind env = bind :: env

let rec apply_env env n is_letrec =
  match env with
  | [] -> raise Impossible
  | ValBind saved_val :: tl ->
    if n = 0 then
      if is_letrec then
        let ProcVal (p_body, _) = saved_val in
        ProcVal (p_body, env)
      else
        saved_val
    else
      apply_env tl (n - 1) is_letrec

exception Interpreter_error of string * Ploc.t

let rec value_of exp env =
  match exp with
  | NLConstExp (num, loc) -> NumVal num
  | NLDiffExp (exp1, exp2, loc) ->
    let eval1 = value_of exp1 env in
    let eval2 = value_of exp2 env in
    (match (eval1, eval2) with
     | (NumVal num1, NumVal num2) -> NumVal (num1 - num2)
     | _ -> raise (Interpreter_error ("the operands of diff should be numbers", loc)))
  | NLIsZeroExp (exp1, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | NumVal num1 -> BoolVal (num1 = 0)
     | _ -> raise (Interpreter_error ("the operand of is_zero should be a number", loc)))
  | NLIfExp (exp1, exp2, exp3, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | BoolVal bool1 -> if bool1 then value_of exp2 env else value_of exp3 env
     | _ -> raise (Interpreter_error ("the predicate of if should be a boolean", loc)))
  | NLVarExp (n, loc) -> apply_env env n false
  | NLLetExp (exp1, body, loc) ->
    let eval1 = value_of exp1 env in
    value_of body (extend_env (ValBind eval1) env)
  | NLProcExp (body, loc) -> ProcVal (body, env)
  | NLCallExp (rator, rand, loc) ->
    let rator_val = value_of rator env in
    (match rator_val with
     | ProcVal proc -> let rand_val = value_of rand env in apply_procedure proc rand_val
     | _ -> raise (Interpreter_error ("the operator of call shoud be a procedure", loc)))
  | NLCondExp (clauses, loc) ->
    let rec inner clauses =
      (match clauses with
       | [] -> raise (Interpreter_error ("none of the conditional clauses evaluates to true", loc))
       | (exp1, exp2) :: tl ->
         let eval1 = value_of exp1 env in
         (match eval1 with
          | BoolVal true -> value_of exp2 env
          | BoolVal false -> inner tl
          | _ -> raise (Interpreter_error ("all clauses should have a boolean-valued condition", loc)))) in
    inner clauses
  | NLLetrecExp (p_body, letrec_body, loc) ->
    value_of letrec_body (extend_env (ValBind (ProcVal (p_body, env))) env)
  | NLLetrecVarExp (n, loc) -> apply_env env n true

and apply_procedure proc arg_val =
  match proc with
  | (body, saved_env) -> value_of body (extend_env (ValBind arg_val) saved_env)

let value_of_top_level top env =
  match top with
  | NLExpTop exp1 ->
    let eval1 = value_of exp1 env in
    (eval1 |> string_of_expval |> prefix "val it = " |> suffix ";" |> print_endline);
    extend_env (ValBind eval1) env
  | NLValTop (var, exp1) ->
    let eval1 = value_of exp1 env in
    (eval1 |> string_of_expval |> prefix ("val " ^ var ^ " = ") |> suffix ";" |> print_endline);
    extend_env (ValBind eval1) env

let value_of_program (NLAProgram tops) = List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
