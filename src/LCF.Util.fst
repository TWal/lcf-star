module LCF.Util

open FStar.Tactics

val digit_to_string: n:nat{n<10} -> string
let digit_to_string n =
  match n with
  | 0 -> "0"
  | 1 -> "1"
  | 2 -> "2"
  | 3 -> "3"
  | 4 -> "4"
  | 5 -> "5"
  | 6 -> "6"
  | 7 -> "7"
  | 8 -> "8"
  | 9 -> "9"

val nat_to_string: nat -> string
let rec nat_to_string n =
  if n < 10 then
    digit_to_string n
  else
    nat_to_string (n/10) ^ digit_to_string (n % 10)

val join_strings: string -> list string -> string
let rec join_strings joiner l =
  match l with
  | [] -> ""
  | [h] -> h
  | h::t -> h ^ joiner ^ join_strings joiner t


val fv_eq: fv -> fv -> Tac bool
let fv_eq fv1 fv2 =
  term_eq (pack (Tv_FVar fv1)) (pack (Tv_FVar fv2))

val get_lhs_from_lemma: term -> Tac term
let get_lhs_from_lemma t =
  let ty = tc (cur_env ()) t in
  let bs, c = collect_arr_bs ty in
  let e =
      try cur_env ()
      with _ -> top_env ()
  in
  let e = fold_right (fun b acc -> push_binder acc b) bs e in
  match inspect_comp c with
  | C_Lemma pre post _ ->
    begin
      let post = `((`#post) ()) in (* unthunk *)
      let post = norm_term_env e [] post in
      let (h, ts) = collect_app post in
      if term_eq h (`eq2) then (
        match ts with
        | [(ty, Q_Implicit); (lhs, Q_Explicit); (rhs, Q_Explicit)] ->
          lhs
        | _ -> fail "not an equality (==)"
      ) else (
        fail "not an equality (==)"
      )
    end
  | _ -> fail "not a lemma"
