open Syntax

type environment = (string * expval) list

and expval =
  | NumVal of int
  | BoolVal of bool
  | ListVal of expval list

let rec string_of_expval eval =
  match eval with
  | NumVal num -> string_of_int num
  | BoolVal bool -> string_of_bool bool
  | ListVal evals ->
    match evals with
    | [] -> "()"
    | hd :: tl -> "(" ^ (List.fold_left (fun acc eval -> acc ^ " " ^ string_of_expval eval) (string_of_expval hd) tl) ^ ")"

let empty_env () = []

let extend_env var eval env = (var, eval) :: env

let apply_env env var = List.assoc var env

exception Interpreter_error of string * Ploc.t

let rec value_of exp env =
  match exp with
  | ConstExp (num, loc) -> NumVal num
  | BopExp (bop, exp1, exp2, loc) ->
    let eval1 = value_of exp1 env in
    let eval2 = value_of exp2 env in
    (match bop with
     | Diff ->
       (match (eval1, eval2) with
        | (NumVal num1, NumVal num2) -> NumVal (num1 - num2)
        | _ -> raise (Interpreter_error ("the operands of diff should be numbers", loc)))
     | Add ->
       (match (eval1, eval2) with
        | (NumVal num1, NumVal num2) -> NumVal (num1 + num2)
        | _ -> raise (Interpreter_error ("the operands of add should be numbers", loc)))
     | Mult ->
       (match (eval1, eval2) with
        | (NumVal num1, NumVal num2) -> NumVal (num1 * num2)
        | _ -> raise (Interpreter_error ("the operands of mult should be numbers", loc)))
     | Quot ->
       (match (eval1, eval2) with
        | (NumVal num1, NumVal num2) -> if num2 != 0 then NumVal (num1 / num2) else raise (Interpreter_error ("the second operand should be non-zero", loc))
        | _ -> raise (Interpreter_error ("the operands of quot should be numbers", loc)))
     | IsEqual ->
       (match (eval1, eval2) with
        | (NumVal num1, NumVal num2) -> BoolVal (num1 = num2)
        | _ -> raise (Interpreter_error ("the operands of is_equal should be numbers", loc)))
     | IsGreater ->
       (match (eval1, eval2) with
        | (NumVal num1, NumVal num2) -> BoolVal (num1 > num2)
        | _ -> raise (Interpreter_error ("the operands of is_greater should be numbers", loc)))
     | IsLess ->
       (match (eval1, eval2) with
        | (NumVal num1, NumVal num2) -> BoolVal (num1 < num2)
        | _ -> raise (Interpreter_error ("the operands of is_less should be numbers", loc)))
     | Cons ->
       (match eval2 with
        | ListVal list2 -> ListVal (eval1 :: list2)
        | _ -> raise (Interpreter_error ("the second operand of cons should be a list", loc))))
  | UopExp (uop, exp1, loc) ->
    let eval1 = value_of exp1 env in
    (match uop with
     | IsZero ->
       (match eval1 with
        | NumVal num1 -> BoolVal (num1 = 0)
        | _ -> raise (Interpreter_error ("the operand of is_zero should be a number", loc)))
     | Minus ->
       (match eval1 with
        | NumVal num1 -> NumVal (- num1)
        | _ -> raise (Interpreter_error ("the operand of minus should be a number", loc)))
     | Car ->
       (match eval1 with
        | ListVal list1 -> if List.length list1 > 0 then List.hd list1 else raise (Interpreter_error ("the operand of car should be non-empty", loc))
        | _ -> raise (Interpreter_error ("the operand of car should be a list", loc)))
     | Cdr ->
       (match eval1 with
        | ListVal list1 -> if List.length list1 > 0 then ListVal (List.tl list1) else raise (Interpreter_error ("the operand of cdr should be non-empty", loc))
        | _ -> raise (Interpreter_error ("the operand of cdr should be a list", loc)))
     | IsNull ->
       (match eval1 with
        | ListVal list1 -> BoolVal (List.length list1 = 0)
        | _ -> raise (Interpreter_error ("the operand of is_null should be a list", loc))))
  | IfExp (exp1, exp2, exp3, loc) ->
    let eval1 = value_of exp1 env in
    (match eval1 with
     | BoolVal bool1 -> if bool1 then value_of exp2 env else value_of exp3 env
     | _ -> raise (Interpreter_error ("the predicate of if should be a boolean", loc)))
  | VarExp (var, loc) ->
    (try apply_env env var
     with Not_found -> raise (Interpreter_error ("the variable " ^ var ^ " is not in the environment", loc)))
  | LetExp (binds, body, loc) ->
    let iter new_env (var, exp1) = extend_env var (value_of exp1 env) new_env in
    value_of body (List.fold_left iter env binds)
  | LetSeqExp (binds, body, loc) ->
    let iter new_env (var, exp1) = extend_env var (value_of exp1 new_env) new_env in
    value_of body (List.fold_left iter env binds)
  | EmptylistExp loc -> ListVal []
  | ListExp (exps, loc) -> ListVal (List.map (fun exp1 -> value_of exp1 env) exps)
  | CondExp (clauses, loc) ->
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
  | PrintExp (exp1, loc) ->
    let eval1 = value_of exp1 env in
    print_endline (string_of_expval eval1); NumVal 1

let value_of_top_level (ExpTop exp1) =
  value_of exp1 (empty_env ()) |> string_of_expval |> print_endline

let value_of_program (AProgram tops) = List.iter value_of_top_level tops
