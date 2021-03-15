module LCF.Util

open FStar.Tactics
open LCF.Map //for cmp_on



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


val fv_eq: fv -> fv -> bool
let fv_eq fv1 fv2 =
  (inspect_fv fv1) = (inspect_fv fv2)

val option_to_list: #a:Type -> option a -> list a
let option_to_list opt =
  match opt with
  | Some x -> [x]
  | None -> []

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

val concat_map: #a:Type -> #b:Type -> (a -> Tac (list b)) -> list a -> Tac (list b)
let rec concat_map #a #b f l =
  match l with
  | [] -> []
  | h::t -> (f h)@(concat_map f t)

val cmp_on_int: cmp_on int
let cmp_on_int x y =
  if x < y then Lt
  else if x = y then Eq
  else Gt

val cmp_on_nat: cmp_on nat
let cmp_on_nat =
  cmp_on_int


val cmp_on_char: cmp_on FStar.Char.char
let cmp_on_char c1 c2 =
  cmp_on_int (FStar.Char.int_of_char c1) (FStar.Char.int_of_char c2)

//TODO: use String.Compare?
val cmp_on_string: cmp_on string
let cmp_on_string s1 s2 =
  cmp_on_list cmp_on_char (FStar.String.list_of_string s1) (FStar.String.list_of_string s2)

val cmp_on_fv: cmp_on fv
let cmp_on_fv fv1 fv2 =
  cmp_on_list cmp_on_string (inspect_fv fv1) (inspect_fv fv2)
