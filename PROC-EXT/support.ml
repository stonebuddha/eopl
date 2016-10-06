let set_minus eq s1 s2 =
  List.filter (fun x -> not (List.exists (fun y -> eq x y) s2)) s1

let set_union eq s1 s2 =
  s1 @ set_minus eq s2 s1
