let set_minus eq s1 s2 =
  List.filter (fun x -> not (List.exists (fun y -> eq x y) s2)) s1

let set_union eq s1 s2 =
  s1 @ set_minus eq s2 s1

let string_of_loc loc =
  let fp = Ploc.first_pos loc in
  let lp = Ploc.last_pos loc in
  let ln = Ploc.line_nb loc in
  let lnl = Ploc.line_nb_last loc in
  let bp = Ploc.bol_pos loc in
  let bpl = Ploc.bol_pos_last loc in
  string_of_int ln ^ "-" ^ string_of_int lnl ^ ":" ^ string_of_int (fp - bp + 1) ^ "-" ^ string_of_int (lp - bpl)
