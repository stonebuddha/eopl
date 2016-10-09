open Syntax

let empty_senv () = []

let extend_senv vars senv = vars :: senv

let rec apply_senv senv var =
  let rec inner env var =
    (match env with
     | [] -> raise Not_found
     | (saved_var, is_letrec) :: saved_env ->
       if var = saved_var then (0, is_letrec) else let (res, is_letrec) = inner saved_env var in (1 + res, is_letrec)) in
  match senv with
  | [] -> raise Not_found
  | saved_vars :: saved_senv ->
    try let (who, is_letrec) = inner saved_vars var in ((0, who), is_letrec)
    with Not_found -> let ((dep, who), is_letrec) = apply_senv saved_senv var in ((dep + 1, who), is_letrec)

exception Translator_error of string * Ploc.t

let rec translation_of exp senv =
  match exp with
  | ConstExp (num, loc) -> NLConstExp (num, loc)
  | DiffExp (exp1, exp2, loc) ->
    let nlexp1 = translation_of exp1 senv in
    let nlexp2 = translation_of exp2 senv in
    NLDiffExp (nlexp1, nlexp2, loc)
  | IsZeroExp (exp1, loc) ->
    let nlexp1 = translation_of exp1 senv in
    NLIsZeroExp (nlexp1, loc)
  | IfExp (exp1, exp2, exp3, loc) ->
    let nlexp1 = translation_of exp1 senv in
    let nlexp2 = translation_of exp2 senv in
    let nlexp3 = translation_of exp3 senv in
    NLIfExp (nlexp1, nlexp2, nlexp3, loc)
  | VarExp (var, loc) ->
    (try
       let ((dep, who), is_letrec) = apply_senv senv var in
       if is_letrec then NLLetrecVarExp ((dep, who), loc) else NLVarExp ((dep, who), loc)
     with Not_found -> raise (Translator_error ("the variable " ^ var ^ " is not bound", loc)))
  | LetExp (binds, body, loc) ->
    let nlexps = List.map (fun (_, exp1) -> translation_of exp1 senv) binds in
    let nlbody = translation_of body (extend_senv (List.rev (List.map (fun (var, _) -> (var, false)) binds)) senv) in
    NLLetExp (nlexps, nlbody, loc)
  | ProcExp (vars, body, loc) ->
    let nlbody = translation_of body (extend_senv (List.rev (List.map (fun var -> (var, false)) vars)) senv) in
    NLProcExp (nlbody, loc)
  | CallExp (rator, rands, loc) ->
    let nlrator = translation_of rator senv in
    let nlrands = List.map (fun rand -> translation_of rand senv) rands in
    NLCallExp (nlrator, nlrands, loc)
  | CondExp (clauses, loc) ->
    let nlclausess = List.map (fun (exp1, exp2) -> (translation_of exp1 senv, translation_of exp2 senv)) clauses in
    NLCondExp (nlclausess, loc)
  | LetrecExp (binds, letrec_body, loc) ->
    let letrec_body_senv = extend_senv (List.rev (List.map (fun (p_name, _, _) -> (p_name, true)) binds)) senv in
    let p_bodies = List.map (fun (_, b_vars, p_body) -> translation_of p_body (extend_senv (List.rev (List.map (fun b_var -> (b_var, false)) b_vars)) letrec_body_senv)) binds in
    NLLetrecExp (p_bodies, translation_of letrec_body letrec_body_senv, loc)

let rec translation_of_top_level top senv =
  match top with
  | ExpTop exp1 ->
    let nlexp1 = translation_of exp1 senv in
    (NLExpTop nlexp1, extend_senv [("it", false)] senv)
  | ValTop (var, exp1) ->
    let nlexp1 = translation_of exp1 senv in
    (NLValTop (var, nlexp1), extend_senv [(var, false)] senv)

let translation_of_program (AProgram tops) =
  NLAProgram ((List.fold_left
                 (fun (senv, rev_nltops) top ->
                    let (nltop, new_senv) = translation_of_top_level top senv in
                    (new_senv, nltop :: rev_nltops)) (empty_senv (), []) tops) |> snd |> List.rev)
