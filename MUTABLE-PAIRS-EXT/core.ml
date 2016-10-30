open Syntax

type refer = int

and mutarray = refer * int

and store = expval list

and environment = refer list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ProcVal of proc
  | MutpairVal of refer
  | ArrayVal of mutarray

and proc = expression * environment ref

let string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ProcVal _ -> "<proc>"
  | MutpairVal _ -> "<mutpair>"
  | ArrayVal (_, len) -> "<array[" ^ string_of_int len ^ "]>"

let empty_env () = []

let extend_env refer env = refer :: env

let apply_env env var = List.nth env var

let empty_store () = ref []

let init_store st = st := []

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

let the_store = empty_store ()

exception Interpreter_error of string * Ploc.t

let make_pair eval1 eval2 st =
  let refer1 = newref eval1 st in
  let refer2 = newref eval2 st in
  refer1

let left p st = deref p st

let right p st = deref (p + 1) the_store

let setleft p eval st = setref p eval st

let setright p eval st = setref (p + 1) eval st

let make_array len eval st =
  let refer = newref eval st in
  let rec inner len =
    if len > 0 then
      let _ = newref eval st in
      inner (len - 1)
    else
      () in
  let () = inner (len - 1) in
  refer

let arrayref (arr, len) idx st =
  if 0 <= idx && idx < len then
    deref (arr + idx) st
  else
    raise Not_found

let arrayset (arr, len) idx eval st =
  if 0 <= idx && idx < len then
    setref (arr + idx) eval st
  else
    raise Not_found

let arraylength (_, len) _ = len

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
    let env' = List.fold_left (fun env eval1 -> extend_env (newref eval1 the_store) env) env evals in
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
    let env' = List.fold_left (fun env eval -> extend_env (newref eval the_store) env) env procs in
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
  | NewpairExp (exp1, exp2, loc) ->
    let eval1 = value_of exp1 env in
    let eval2 = value_of exp2 env in
    MutpairVal (make_pair eval1 eval2 the_store)
  | LeftExp (exp1, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | MutpairVal p -> left p the_store
     | _ -> raise (Interpreter_error ("the operand of left should be a mutpair", loc)))
  | RightExp (exp1, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | MutpairVal p -> right p the_store
     | _ -> raise (Interpreter_error ("the operand of right should be a mutpair", loc)))
  | SetleftExp (exp1, exp2, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | MutpairVal p -> let eval2 = value_of exp2 env in let () = setleft p eval2 the_store in NumVal 82
     | _ -> raise (Interpreter_error ("the first operand of setleft should be a mutpair", loc)))
  | SetrightExp (exp1, exp2, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | MutpairVal p -> let eval2 = value_of exp2 env in let () = setright p eval2 the_store in NumVal 83
     | _ -> raise (Interpreter_error ("the first operand of setright should be a mutpair", loc)))
  | NewarrayExp (exp1, exp2, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | NumVal len ->
       if len <= 0 then raise (Interpreter_error ("the length of array should be positive", loc))
       else let eval2 = value_of exp2 env in ArrayVal (make_array len eval2 the_store, len)
     | _ -> raise (Interpreter_error ("the length of array should be a number", loc)))
  | ArrayrefExp (exp1, exp2, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | ArrayVal a ->
       let eval2 = value_of exp2 env in
       (match eval2 with
        | NumVal idx -> (try arrayref a idx the_store with Not_found -> raise (Interpreter_error ("the index of arrayref is illegal", loc)))
        | _ -> raise (Interpreter_error ("the index of arrayref should be a number", loc)))
     | _ -> raise (Interpreter_error ("the first operand of arrayref should be an array", loc)))
  | ArraysetExp (exp1, exp2, exp3, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | ArrayVal a ->
       let eval2 = value_of exp2 env in
       (match eval2 with
        | NumVal idx ->
          let eval3 = value_of exp3 env in
          (try let () = arrayset a idx eval3 the_store in NumVal 91 with Not_found -> raise (Interpreter_error ("the index of arrayset is illegal", loc)))
        | _ -> raise (Interpreter_error ("the index of arrayset should be a number", loc)))
     | _ -> raise (Interpreter_error ("the first operand of arrayset should be an array", loc)))
  | ArraylengthExp (exp1, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | ArrayVal a -> NumVal (arraylength a the_store)
     | _ -> raise (Interpreter_error ("the operand of arraylength should be an array", loc)))

and apply_procedure proc arg_val =
  match proc with
  | (body, saved_env) -> value_of body (extend_env (newref arg_val the_store) !saved_env)

let value_of_top_level top env =
  match top with
  | ValTop (var, exp1) ->
    let eval1 = value_of exp1 env in
    let () = print_endline ("val " ^ var ^ " = " ^ string_of_expval eval1 ^ ";") in
    extend_env (newref eval1 the_store) env
  | FunTop (p_name, p_body) ->
    let saved_env = ref (empty_env ()) in
    let proc = ProcVal (p_body, saved_env) in
    let () = saved_env := extend_env (newref proc the_store) env in
    !saved_env

let value_of_program (AProgram tops) =
  let () = init_store the_store in
  List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
