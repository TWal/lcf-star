module LCF.Net.Test

open FStar.Tactics
open LCF.Net.BottomUp
open LCF.Util

val add_lemma: #a:Type0 -> net a -> term -> a -> Tac (net a)
let add_lemma #a net t x =
  let lhs = get_lhs_from_lemma t in
  add_term net lhs x

assume val length_append: #a:Type -> l1:list a -> l2:list a -> Lemma (List.Tot.length (l1@l2) == (List.Tot.length l1) + (List.Tot.length l2))
assume val length_append_nil: #a:Type -> l1:list a -> Lemma (List.Tot.length (l1@[]) == (List.Tot.length l1))
assume val append_nil: #a:Type -> l:list a -> Lemma (l@[] == l)
assume val length_cons: #a:Type -> x:a -> l:list a -> Lemma (List.Tot.length (x::l) == (List.Tot.length l) + 1)

let mk_net (l:list term): Tac (net string) =
  Tactics.Util.fold_left (fun net t ->
    add_lemma net t (term_to_string t)
  ) empty_net l

let test (x:int) (l:list int) =
  assert (List.Tot.length (l@[]) + 1 == List.Tot.length (x::l)) by (
    let net = mk_net [(`length_append); (`append_nil); (`length_cons); (`length_append_nil)] in
    ctrl_rewrite TopDown
    (
      fun t ->
        let matches = (match_term net t) in
        if matches <> [] then (
          print ((term_to_string t) ^ "\n" ^ (join_strings ", " (match_term net t)) ^ "\n")
        ) else ();
        (false, Continue)
    )
    (
      fun () -> trefl()
    );
    tadmit ()
  )
