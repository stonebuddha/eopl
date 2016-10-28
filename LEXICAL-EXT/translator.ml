open Syntax

let empty_senv () = []

let extend_senv vars senv = vars :: senv

let rec apply_senv senv var =
  let rec inner env var =
    (match env with
     | [] -> raise Not_found
     | saved_var :: saved_env ->
       if var = saved_var then 0 else let res = inner saved_env var in 1 + res) in
  match senv with
  | [] -> raise Not_found
  | saved_vars :: saved_senv ->
    try let who = inner saved_vars var in (0, who)
    with Not_found -> let (dep, who) = apply_senv saved_senv var in (dep + 1, who)

exception Translator_error of string * Ploc.t

let set_union s1 s2 =
  List.append s1 (List.filter (fun e -> not (List.mem e s1)) s2)

let set_diff s1 s2 =
  List.filter (fun e -> not (List.mem e s2)) s1

let rec free_vars exp =
  match exp with
  | ConstExp _ -> []
  | DiffExp (exp1, exp2, _) ->
    let fv1 = free_vars exp1 in
    let fv2 = free_vars exp2 in
    set_union fv1 fv2
  | IsZeroExp (exp1, _) -> free_vars exp1
  | IfExp (exp1, exp2, exp3, _) ->
    let fv1 = free_vars exp1 in
    let fv2 = free_vars exp2 in
    let fv3 = free_vars exp3 in
    set_union fv1 fv2 |> set_union fv3
  | VarExp (var, _) -> [var]
  | LetExp (binds, body, _) ->
    let fv1 = List.fold_left (fun fv (_, exp1) -> set_union fv (free_vars exp1)) [] binds in
    let fv2 = set_diff (free_vars body) (List.map fst binds) in
    set_union fv1 fv2
  | ProcExp (vars, body, _) ->
    set_diff (free_vars body) vars
  | CallExp (rator, rands, _) ->
    let fv1 = free_vars rator in
    let fv2 = List.fold_left set_union [] (List.map free_vars rands) in
    set_union fv1 fv2
  | CondExp (clauses, _) ->
    List.fold_left (fun fv (exp1, exp2) -> set_union (free_vars exp1) (free_vars exp2) |> set_union fv) [] clauses
  | LetrecExp (binds, letrec_body, _) ->
    let fvs = List.map (fun (_, b_vars, p_body) -> set_diff (free_vars p_body) b_vars) binds in
    let p_names = List.map (fun (p_name, _, _) -> p_name) binds in
    let fv1 = set_diff (List.fold_left set_union [] fvs) p_names in
    let fv2 = set_diff (free_vars letrec_body) p_names in
    set_union fv1 fv2

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
       let (dep, who) = apply_senv senv var in
       NLVarExp ((dep, who), loc)
     with Not_found -> raise (Translator_error ("the variable " ^ var ^ " is not bound", loc)))
  | LetExp (binds, body, loc) ->
    let nlexps = List.map (fun (_, exp1) -> translation_of exp1 senv) binds in
    let nlbody = translation_of body (extend_senv (List.rev (List.map fst binds)) senv) in
    NLLetExp (nlexps, nlbody, loc)
  | ProcExp (vars, body, loc) ->
    let fv = free_vars exp in
    let frees = List.map (apply_senv senv) fv in
    let trimmed_senv = extend_senv fv (empty_senv ()) in
    let nlbody = translation_of body (extend_senv (List.rev vars) trimmed_senv) in
    NLProcExp (frees, nlbody, loc)
  | CallExp (rator, rands, loc) ->
    let nlrator = translation_of rator senv in
    let nlrands = List.map (fun rand -> translation_of rand senv) rands in
    NLCallExp (nlrator, nlrands, loc)
  | CondExp (clauses, loc) ->
    let nlclausess = List.map (fun (exp1, exp2) -> (translation_of exp1 senv, translation_of exp2 senv)) clauses in
    NLCondExp (nlclausess, loc)
  | LetrecExp (binds, letrec_body, loc) ->
    let letrec_body_bind = List.rev (List.map (fun (p_name, _, _) -> p_name) binds) in
    let letrec_body_senv = extend_senv letrec_body_bind senv in
    let p_names = List.map (fun (p_name, _, _) -> p_name) binds in
    let p_bodies = List.map (fun (_, b_vars, p_body) ->
        let fv = set_diff (free_vars p_body) (set_union p_names b_vars) in
        let frees = List.map (apply_senv senv) fv in
        let trimmed_senv = extend_senv letrec_body_bind (extend_senv fv (empty_senv ())) in
        (frees, translation_of p_body (extend_senv (List.rev b_vars) trimmed_senv))) binds in
    NLLetrecExp (p_bodies, translation_of letrec_body letrec_body_senv, loc)

let rec translation_of_top_level top senv =
  match top with
  | ExpTop exp1 ->
    let nlexp1 = translation_of exp1 senv in
    (NLExpTop nlexp1, extend_senv ["it"] senv)
  | ValTop (var, exp1) ->
    let nlexp1 = translation_of exp1 senv in
    (NLValTop (var, nlexp1), extend_senv [var] senv)

let translation_of_program (AProgram tops) =
  NLAProgram ((List.fold_left
                 (fun (senv, rev_nltops) top ->
                    let (nltop, new_senv) = translation_of_top_level top senv in
                    (new_senv, nltop :: rev_nltops)) (empty_senv (), []) tops) |> snd |> List.rev)
