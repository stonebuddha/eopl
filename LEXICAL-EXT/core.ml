open Support
open Syntax

type environment = bind list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ProcVal of proc

and proc = nameless_expression * environment

and bind =
  | ValBind of (expval ref) list

let string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ProcVal _ -> "<proc>"

exception Impossible

let empty_env () = []

let extend_env bind env = bind :: env

let rec apply_env env dep who =
  match env with
  | [] -> raise Impossible
  | ValBind saved_vals :: tl ->
    if dep = 0 then
      let saved_val = List.nth saved_vals who in
      saved_val
    else
      apply_env tl (dep - 1) who

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
  | NLVarExp ((dep, who), loc) -> !(apply_env env dep who)
  | NLLetExp (exps, body, loc) ->
    let evals = List.map (fun exp1 -> ref (value_of exp1 env)) exps in
    value_of body (extend_env (ValBind (List.rev evals)) env)
  | NLProcExp (frees, body, loc) ->
    let trimmed_env = extend_env (ValBind (List.map (fun (dep, who) -> apply_env env dep who) frees)) (empty_env ()) in
    ProcVal (body, trimmed_env)
  | NLCallExp (rator, rands, loc) ->
    let rator_val = value_of rator env in
    (match rator_val with
     | ProcVal proc -> let rand_vals = List.map (fun rand -> value_of rand env) rands in apply_procedure proc rand_vals
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
  | NLLetrecExp (p_bodies, letrec_body, loc) ->
    let refs = List.map (fun (frees, p_body) ->
        ref (ProcVal (p_body, extend_env (ValBind (List.map (fun (dep, who) -> apply_env env dep who) frees)) (empty_env ())))) p_bodies in
    let new_env = extend_env (ValBind refs) env in
    let () = List.iter (fun proc -> let ProcVal (p_body, saved_env) = !proc in proc := ProcVal (p_body, ValBind refs :: saved_env)) refs in
    value_of letrec_body new_env

and apply_procedure proc arg_vals =
  match proc with
  | (body, saved_env) -> value_of body (extend_env (ValBind (List.map (fun arg_val -> ref arg_val) (List.rev arg_vals))) saved_env)

let value_of_top_level top env =
  match top with
  | NLExpTop exp1 ->
    let eval1 = value_of exp1 env in
    (eval1 |> string_of_expval |> prefix "val it = " |> suffix ";" |> print_endline);
    extend_env (ValBind [ref eval1]) env
  | NLValTop (var, exp1) ->
    let eval1 = value_of exp1 env in
    (eval1 |> string_of_expval |> prefix ("val " ^ var ^ " = ") |> suffix ";" |> print_endline);
    extend_env (ValBind [ref eval1]) env

let value_of_program (NLAProgram tops) = List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
