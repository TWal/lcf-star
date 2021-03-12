module LCF.Net.HOL4

open FStar.Tactics
open LCF.Util
open LCF.Map

val ofvnat_cmp: option (fv*nat) -> option (fv*nat) -> bool
let ofvnat_cmp x1 x2 =
  match x1, x2 with
  | Some (fv1, n1), Some (fv2, n2) ->
    if n1 = n2 then
      fv_eq fv1 fv2
    else
      false
  | None, None -> true
  | _, _ -> false

noeq type net (a:Type0) =
  | NetEnd: list a -> net a
  | NetCont: map (option (fv*nat)) ofvnat_cmp (net a) -> net a

val empty_net: #a:Type0 -> net a
val add_term: #a:Type0 -> net a -> term -> a -> Tac (net a)
val match_term: #a:Type0 -> net a -> term -> Tac (list a)
val merge_net: #a:Type0 -> net a -> net a -> Tac (list a)

let empty_net #a =
  NetCont map_empty

val add_term_aux: #a:Type0 -> net a -> list term -> a -> Tac (net a)
let rec add_term_aux #a n lt y =
  match lt with
  | [] ->
    begin
      match n with
      | NetEnd ys -> NetEnd (y::ys)
      | NetCont _ -> fail "Net.HOL4.add_term_aux: internal error, net invariant was not preserved (should not be a NetCont)"
    end
  | t::ts ->
    begin
      let (hd, args) = collect_app t in
      let targs = List.Tot.map fst args in
      match n with
      | NetCont m ->
        begin
          let ofvnat =
            match inspect hd with
            | Tv_FVar fv -> Some (fv, List.Tot.length args)
            | _ -> None
          in
          let next_lt = targs@ts in
          let next_lt_empty = match next_lt with | [] -> true | _ -> false in
          let child =
            match map_lookup m ofvnat with
            | Some nchild -> nchild
            | None -> if next_lt_empty then NetEnd [] else empty_net
          in
          let new_child = add_term_aux child (targs@ts) y in
          NetCont (map_insert m ofvnat new_child)
        end
      | NetEnd _ -> fail "Net.HOL4.add_term_aux: internal error, net invariant was not preserved (should not be a NetEnd)"
    end

let add_term #a n t y =
  add_term_aux n [t] y


val match_term_aux: #a:Type0 -> net a -> list term -> Tac (list a)
let rec match_term_aux #a n lt =
  match lt with
  | [] ->
    begin
      match n with
      | NetEnd ys -> ys
      | NetCont _ -> fail "Net.HOL4.match_term_aux internal error, net invariant was not preserved (should not be a NetCont)"
    end
  | t::ts ->
    begin
      let (hd, args) = collect_app t in
      let targs = List.Tot.map fst args in
      match n with
      | NetCont m ->
        begin
          let ys_inspect =
            match inspect hd with
            | Tv_FVar fv ->
              begin
                match map_lookup m (Some (fv, List.Tot.length args)) with
                | Some nchild -> match_term_aux nchild (targs@ts)
                | None -> []
              end
            | _ -> []
          in
          let ys_skip =
            match map_lookup m None with
            | Some nchild -> match_term_aux nchild ts
            | None -> []
          in
          ys_inspect @ ys_skip
        end
      | NetEnd _ -> fail "Net.HOL4.match_term_aux internal error, net invariant was not preserved (should not be a NetEnd)"
    end

let match_term #a n t =
  match_term_aux n [t]

let merge_net #a n1 n2 = fail "Net.HOL4.merge_net: not implemented"
