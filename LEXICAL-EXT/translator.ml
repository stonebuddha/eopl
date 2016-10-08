open Syntax

let empty_senv () = []

let extend_senv var is_letrec senv = (var, is_letrec) :: senv

let rec apply_senv senv var =
  match senv with
  | [] -> raise Not_found
  | (saved_var, is_letrec) :: saved_senv ->
    if var = saved_var then (0, is_letrec) else let (res, is_letrec) = apply_senv saved_senv var in (1 + res, is_letrec)

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
       let (n, is_letrec) = apply_senv senv var in
       if is_letrec then NLLetrecVarExp (n, loc) else NLVarExp (n, loc)
     with Not_found -> raise (Translator_error ("the variable " ^ var ^ " is not bound", loc)))
  | LetExp (var, exp1, body, loc) ->
    let nlexp1 = translation_of exp1 senv in
    let nlbody = translation_of body (extend_senv var false senv) in
    NLLetExp (nlexp1, nlbody, loc)
  | ProcExp (var, body, loc) ->
    let nlbody = translation_of body (extend_senv var false senv) in
    NLProcExp (nlbody, loc)
  | CallExp (rator, rand, loc) ->
    let nlrator = translation_of rator senv in
    let nlrand = translation_of rand senv in
    NLCallExp (nlrator, nlrand, loc)
  | CondExp (clauses, loc) ->
    let nlclausess = List.map (fun (exp1, exp2) -> (translation_of exp1 senv, translation_of exp2 senv)) clauses in
    NLCondExp (nlclausess, loc)
  | LetrecExp (p_name, b_var, p_body, letrec_body, loc) ->
    NLLetrecExp (translation_of p_body (extend_senv b_var false (extend_senv p_name true senv)), translation_of letrec_body (extend_senv p_name true senv), loc)

let rec translation_of_top_level top senv =
  match top with
  | ExpTop exp1 ->
    let nlexp1 = translation_of exp1 senv in
    (NLExpTop nlexp1, extend_senv "it" false senv)
  | ValTop (var, exp1) ->
    let nlexp1 = translation_of exp1 senv in
    (NLValTop (var, nlexp1), extend_senv var false senv)

let translation_of_program (AProgram tops) =
  NLAProgram ((List.fold_left
                 (fun (senv, rev_nltops) top ->
                    let (nltop, new_senv) = translation_of_top_level top senv in
                    (new_senv, nltop :: rev_nltops)) (empty_senv (), []) tops) |> snd |> List.rev)
