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
  | VarExp (var, loc) -> deref (apply_env env var) the_store
  | LetExp (exps, body, loc) ->
    let evals = List.map (fun exp1 -> value_of exp1 env) exps in
    let env' =
      try List.fold_left (fun env eval1 -> extend_env (newref eval1 the_store) env) env evals
      with Not_found -> raise (Interpreter_error ("there is no space in the store", loc)) in
    value_of body env'
  | ProcExp (body, loc) -> ProcVal (body, ref env)
  | CallExp (rator, rand, loc) ->
    let rator_val = value_of rator env in
    (match rator_val with
     | ProcVal proc -> let rand_val = value_of rand env in apply_procedure proc rand_val loc
     | _ -> raise (Interpreter_error ("the operator of call should be a procedure", loc)))
  | LetrecExp (p_bodies, letrec_body, loc) ->
    let saved_env = ref (empty_env ()) in
    let procs = List.map (fun p_body -> ProcVal (p_body, saved_env)) p_bodies in
    let env' =
      try List.fold_left (fun env eval -> extend_env (newref eval the_store) env) env procs
      with Not_found -> raise (Interpreter_error ("there is no space in the store", loc)) in
    let () = saved_env := env' in
    value_of letrec_body !saved_env
  | BeginExp (exps, loc) ->
    let eval1 = value_of (List.hd exps) env in
    List.fold_left (fun _ exp1 -> value_of exp1 env) eval1 (List.tl exps)
  | AssignExp (var, exp1, loc) ->
    let refer = apply_env env var in
    let eval1 = value_of exp1 env in
    let () = setref refer eval1 the_store in
    NumVal 27
  | SetdynamicExp (var, exp1, body, loc) ->
    let eval1 = value_of exp1 env in
    let refer = apply_env env var in
    let backup = deref refer the_store in
    let () = setref refer eval1 the_store in
    let eval = value_of body env in
    let () = setref refer backup the_store in
    eval

and apply_procedure proc arg_val loc =
  match proc with
  | (body, saved_env) ->
    let env =
      try extend_env (newref arg_val the_store) !saved_env
      with Not_found -> raise (Interpreter_error ("there is no space in the store", loc)) in
    value_of body env

let value_of_top_level top env =
  match top with
  | ValTop (var, exp1, loc) ->
    let eval1 = value_of exp1 env in
    let () = print_endline ("val " ^ var ^ " = " ^ string_of_expval eval1 ^ ";") in
    (try extend_env (newref eval1 the_store) env
     with Not_found -> raise (Interpreter_error ("there is no space in the store", loc)))
  | FunTop (p_name, p_body, loc) ->
    let saved_env = ref (empty_env ()) in
    let proc = ProcVal (p_body, saved_env) in
    let () =
      try saved_env := extend_env (newref proc the_store) env
      with Not_found -> raise (Interpreter_error ("there is no space in the store", loc)) in
    !saved_env

let value_of_program (AProgram tops) =
  let () = init_store the_store in
  List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
