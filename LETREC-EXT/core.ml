open Support
open Syntax

type environment = (string * bind) list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ProcVal of proc

and proc = string list * expression * environment

and bind =
  | ValBind of expval
  | RecBind of expval ref

let string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ProcVal _ -> "<proc>"

let empty_env () = []

let extend_env var bind env = (var, bind) :: env

let rec apply_env env var =
  let bd = List.assoc var env in
  match bd with
  | ValBind saved_val -> saved_val
  | RecBind mut_saved_val -> !mut_saved_val

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
    value_of body (extend_env var (ValBind  eval1) env)
  | ProcExp (vars, body, loc) -> ProcVal (vars, body, env)
  | CallExp (rator, rands, loc) ->
    let rator_val = value_of rator env in
    (match rator_val with
     | ProcVal proc -> let rand_vals = List.map (fun rand -> value_of rand env) rands in apply_procedure proc rand_vals loc
     | _ -> raise (Interpreter_error ("the operator of call should be a procedure", loc)))
  | LetrecExp (binds, letrec_body, loc) ->
    let (new_env, refs) =
      List.fold_left
        (fun (new_env, refs) (p_name, b_vars, p_body) ->
           let mut_proc = ref (ProcVal (b_vars, p_body, [])) in
           (extend_env p_name (RecBind mut_proc) new_env, mut_proc :: refs)) (env, []) binds in
    let () = List.iter (fun mut_proc -> let ProcVal (b_vars, p_body, _) = !mut_proc in mut_proc := ProcVal (b_vars, p_body, new_env)) refs in
    value_of letrec_body new_env

and apply_procedure proc arg_vals call_site =
  match proc with
  | (vars, body, saved_env) ->
    if List.length arg_vals = List.length vars then
      value_of body (List.fold_left (fun env (var, arg_val) -> extend_env var (ValBind arg_val) env) saved_env (List.combine vars arg_vals))
    else
      raise (Interpreter_error ("the parameters and arguments are not consistent at call site", call_site))

let value_of_top_level top env =
  match top with
  | ExpTop exp1 ->
    let eval1 = value_of exp1 env in
    (eval1 |> string_of_expval |> prefix "val it = " |> suffix ";" |> print_endline);
    extend_env "it" (ValBind eval1) env
  | ValTop (var, exp1) ->
    let eval1 = value_of exp1 env in
    (eval1 |> string_of_expval |> prefix ("val " ^ var ^ " = ") |> suffix ";" |> print_endline);
    extend_env var (ValBind eval1) env
  | RecTop (p_name, b_vars, p_body) ->
    let mut_proc = ref (ProcVal (b_vars, p_body, [])) in
    let new_env = extend_env p_name (RecBind mut_proc) env in
    let ProcVal (b_vars, p_body, _) = !mut_proc in
    let () = mut_proc := ProcVal (b_vars, p_body, new_env) in
    let proc_val = !mut_proc in
    (proc_val |> string_of_expval |> prefix ("val " ^ p_name ^ " = ") |> suffix ";" |> print_endline);
    new_env

let value_of_program (AProgram tops) = List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
