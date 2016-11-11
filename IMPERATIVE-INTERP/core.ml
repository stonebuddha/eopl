open Syntax

type refer = int

and store = expval list

and environment = expval list

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

let extend_env eval env = eval :: env

let apply_env env var = List.nth env var

exception Interpreter_error of string * Ploc.t

type continuation =
  | EndCont
  | DiffFstCont of expression * environment * continuation * Ploc.t
  | DiffSndCont of expval * continuation * Ploc.t
  | IsZeroCont of continuation * Ploc.t
  | IfCont of expression * expression * environment * continuation * Ploc.t
  | LetCont of expval list * expression list * expression * environment * continuation * Ploc.t
  | CallRatorCont of expression * environment * continuation * Ploc.t
  | CallRandCont of proc * continuation * Ploc.t

type bounce =
  | Ans of expval
  | Jump of (unit -> bounce)

let g_exp : (expression option) ref = ref None
let g_env : (environment option) ref = ref None
let g_cont : (continuation option) ref = ref None
let g_eval : (expval option) ref = ref None
let g_proc : (proc option) ref = ref None
let g_pc : (bounce option) ref = ref None

let get op =
  match op with
  | Some x -> x
  | _ -> raise Not_found

let rec value_of_k () =
  match get (!g_exp) with
  | ConstExp (num, loc) ->
    let () = g_eval := Some (NumVal num) in
    apply_cont ()
  | DiffExp (exp1, exp2, loc) ->
    let () = g_cont := Some (DiffFstCont (exp2, get (!g_env), get (!g_cont), loc)) in
    let () = g_exp := Some exp1 in
    value_of_k ()
  | IsZeroExp (exp1, loc) ->
    let () = g_cont := Some (IsZeroCont (get (!g_cont), loc)) in
    let () = g_exp := Some exp1 in
    value_of_k ()
  | IfExp (exp1, exp2, exp3, loc) ->
    let () = g_cont := Some (IfCont (exp2, exp3, get (!g_env), get (!g_cont), loc)) in
    let () = g_exp := Some exp1 in
    value_of_k ()
  | VarExp (var, loc) ->
    let () = g_eval := Some (apply_env (get (!g_env)) var) in
    apply_cont ()
  | LetExp (exps, body, loc) ->
    (match exps with
     | [] ->
       let () = g_exp := Some body in
       value_of_k ()
     | exp1 :: exps' ->
       let () = g_cont := Some (LetCont ([], exps', body, get (!g_env), get (!g_cont), loc)) in
       let () = g_exp := Some exp1 in
       value_of_k ())
  | ProcExp (body, loc) ->
    let () = g_eval := Some (ProcVal (body, ref (get (!g_env)))) in
    apply_cont ()
  | CallExp (rator, rand, loc) ->
    let () = g_cont := Some (CallRatorCont (rand, get (!g_env), get (!g_cont), loc)) in
    let () = g_exp := Some rator in
    value_of_k ()
  | LetrecExp (p_bodies, letrec_body, loc) ->
    let saved_env = ref (empty_env ()) in
    let procs = List.map (fun p_body -> ProcVal (p_body, saved_env)) p_bodies in
    let env' = List.fold_left (fun env eval -> extend_env eval env) (get (!g_env)) procs in
    let () = saved_env := env' in
    let () = g_exp := Some letrec_body in
    let () = g_env := Some (!saved_env) in
    value_of_k ()

and apply_procedure_k () =
  match get (!g_proc) with
  | (body, saved_env) ->
    let () = g_exp := Some body in
    let () = g_env := Some (extend_env (get (!g_eval)) !saved_env) in
    Jump value_of_k

and apply_cont () =
  match get (!g_cont) with
  | EndCont -> Ans (get (!g_eval))
  | DiffFstCont (exp2, env, saved_cont, loc) ->
    let () = g_cont := Some (DiffSndCont (get (!g_eval), saved_cont, loc)) in
    let () = g_exp := Some exp2 in
    let () = g_env := Some env in
    value_of_k ()
  | DiffSndCont (eval1, saved_cont, loc) ->
    let eval2 = get (!g_eval) in
    (match (eval1, eval2) with
     | (NumVal num1, NumVal num2) ->
       let () = g_cont := Some saved_cont in
       let () = g_eval := Some (NumVal (num1 - num2)) in
       apply_cont ()
     | _ -> raise (Interpreter_error ("the operands of diff should be numbers", loc)))
  | IsZeroCont (saved_cont, loc) ->
    let eval1 = get (!g_eval) in
    (match eval1 with
     | NumVal num1 ->
       let () = g_cont := Some saved_cont in
       let () = g_eval := Some (BoolVal (num1 = 0)) in
       apply_cont ()
     | _ -> raise (Interpreter_error ("the operand of is_zero should be a number", loc)))
  | IfCont (exp2, exp3, env, saved_cont, loc) ->
    let eval1 = get (!g_eval) in
    (match eval1 with
     | BoolVal bool1 ->
       if bool1 then
         let () = g_cont := Some saved_cont in
         let () = g_exp := Some exp2 in
         let () = g_env := Some env in
         value_of_k ()
       else
         let () = g_cont := Some saved_cont in
         let () = g_exp := Some exp3 in
         let () = g_env := Some env in
         value_of_k ()
     | _ -> raise (Interpreter_error ("the predicate of if should be a boolean", loc)))
  | LetCont (evals, exps, body, env, saved_cont, loc) ->
    let eval1 = get (!g_eval) in
    let evals' = eval1 :: evals in
    (match exps with
     | [] ->
       let env' = List.fold_right extend_env evals' env in
       let () = g_cont := Some saved_cont in
       let () = g_exp := Some body in
       let () = g_env := Some env' in
       value_of_k ()
     | exp1 :: exps' ->
       let () = g_cont := Some (LetCont (evals', exps', body, env, saved_cont, loc)) in
       let () = g_exp := Some exp1 in
       let () = g_env := Some env in
       value_of_k ())
  | CallRatorCont (rand, env, saved_cont, loc) ->
    let rator_val = get (!g_eval) in
    (match rator_val with
     | ProcVal proc ->
       let () = g_cont := Some (CallRandCont (proc, saved_cont, loc)) in
       let () = g_exp := Some rand in
       let () = g_env := Some env in
       value_of_k ()
     | _ -> raise (Interpreter_error ("the operator of call should be a procedure", loc)))
  | CallRandCont (proc, saved_cont, loc) ->
    let rand_val = get (!g_eval) in
    let () = g_cont := Some saved_cont in
    let () = g_proc := Some proc in
    let () = g_eval := Some rand_val in
    apply_procedure_k ()

let rec trampoline () =
  match get (!g_pc) with
  | Ans eval -> eval
  | Jump fn ->
    let () = g_pc := Some (fn ()) in
    trampoline ()

let value_of_top_level top env =
  match top with
  | ValTop (var, exp1) ->
    let () = g_cont := Some EndCont in
    let () = g_exp := Some exp1 in
    let () = g_env := Some env in
    let () = g_pc := Some (Jump value_of_k) in
    let eval1 = trampoline () in
    let () = print_endline ("val " ^ var ^ " = " ^ string_of_expval eval1 ^ ";") in
    extend_env eval1 env
  | FunTop (p_name, p_body) ->
    let saved_env = ref (empty_env ()) in
    let proc = ProcVal (p_body, saved_env) in
    let () = saved_env := extend_env proc env in
    let () = print_endline ("fun " ^ p_name ^ " is defined;") in
    !saved_env

let value_of_program (AProgram tops) =
  List.fold_left (fun env top -> value_of_top_level top env) (empty_env ()) tops; ()
