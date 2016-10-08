open Syntax

let empty_senv () = []

let extend_senv var senv = var :: senv

let rec apply_senv senv var =
  match senv with
  | [] -> raise Not_found
  | saved_var :: saved_senv ->
    if var = saved_var then 0 else 1 + apply_senv saved_senv var

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
    (try NLVarExp (apply_senv senv var, loc)
     with Not_found -> raise (Translator_error ("the variable " ^ var ^ " is not bound", loc)))
  | LetExp (var, exp1, body, loc) ->
    let nlexp1 = translation_of exp1 senv in
    let nlbody = translation_of body (extend_senv var senv) in
    NLLetExp (nlexp1, nlbody, loc)
  | ProcExp (var, body, loc) ->
    let nlbody = translation_of body (extend_senv var senv) in
    NLProcExp (nlbody, loc)
  | CallExp (rator, rand, loc) ->
    let nlrator = translation_of rator senv in
    let nlrand = translation_of rand senv in
    NLCallExp (nlrator, nlrand, loc)
  | CondExp (clauses, loc) ->
    let nlclausess = List.map (fun (exp1, exp2) -> (translation_of exp1 senv, translation_of exp2 senv)) clauses in
    NLCondExp (nlclausess, loc)

let rec translation_of_top_level top senv =
  match top with
  | ExpTop exp1 ->
    let nlexp1 = translation_of exp1 senv in
    (NLExpTop nlexp1, extend_senv "it" senv)
  | ValTop (var, exp1) ->
    let nlexp1 = translation_of exp1 senv in
    (NLValTop (var, nlexp1), extend_senv var senv)

let translation_of_program (AProgram tops) =
  NLAProgram ((List.fold_left
                 (fun (senv, rev_nltops) top ->
                    let (nltop, new_senv) = translation_of_top_level top senv in
                    (new_senv, nltop :: rev_nltops)) (empty_senv (), []) tops) |> snd |> List.rev)
