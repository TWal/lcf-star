module LCF.Net.BottomUp

open FStar.Tactics
open LCF.Util
open LCF.Map

// TODO: more efficient associative datastructure
type app_map = map nat (=) (option nat & map nat (=) nat)

noeq type net (a:Type0) =
  {
    fvar: map fv fv_eq nat;
    app: app_map;
    next_state: nat;
    state_to_a: map nat (=) (list a)
  }

val empty_net: #a:Type0 -> net a
let empty_net #a =
  { fvar = map_empty
  ; app = map_empty
  ; next_state = 0
  ; state_to_a = map_empty
  }

val term_to_state: #a:Type0 -> net a -> term -> Tac (list nat)
let rec term_to_state #a trans t =
  match (inspect t) with
  | Tv_FVar fv ->
    begin
      option_to_list (map_lookup trans.fvar fv)
    end
  | Tv_App hd argv ->
    begin
      let sts1 = term_to_state trans hd in
      concat_map (fun st1 ->
        match map_lookup trans.app st1 with
        | None -> []
        | Some (stres, st2map) ->
          if map_is_empty st2map then
            option_to_list stres
          else (
            let sts2 = term_to_state trans (fst argv) in
            (option_to_list stres)@(
              List.Tot.concatMap (fun st2 ->
                option_to_list (map_lookup st2map st2)
              ) sts2
            )
          )
      ) sts1
    end
  | _ -> []

val app_map_lookup: app_map -> (nat & option nat) -> option nat
let app_map_lookup m (v1, ov2) =
  match map_lookup m v1 with
  | None -> None
  | Some (v2none, v2map) ->
    begin
      match ov2 with
      | None -> v2none
      | Some v2 -> map_lookup v2map v2
    end

val app_map_insert: app_map -> (nat & option nat) -> nat -> app_map
let app_map_insert m (v1, ov2) y =
  match map_lookup m v1 with
  | None ->
    begin
      match ov2 with
      | None -> map_insert m v1 (Some y, map_empty)
      | Some v2 -> map_insert m v1 (None, map_insert map_empty v2 y)
    end
  | Some (v2none, v2map) ->
    begin
      match ov2 with
      | None -> map_insert m v1 (Some y, v2map)
      | Some v2 -> map_insert m v1 (v2none, map_insert v2map v2 y)
    end

val add_term_aux: #a:Type0 -> net a -> term -> Tac (net a & option nat)
let rec add_term_aux #a trans t =
  match inspect t with
  | Tv_FVar fv ->
    begin
      let t_state = term_to_state trans t in
      match map_lookup trans.fvar fv with
      | None ->
        (
          { fvar = map_insert trans.fvar fv trans.next_state
          ; app = trans.app
          ; next_state = trans.next_state+1
          ; state_to_a = trans.state_to_a
          },
          Some (trans.next_state)
        )
      | Some st -> (trans, Some st)
      | _ -> fail "BottomUp.add_term_aux: too many states for free variable"
    end
  | Tv_App hd argv ->
    begin
      let (trans, ost1) = add_term_aux trans hd in
      let (trans, ost2) = add_term_aux trans (fst argv) in
      match ost1 with
      | Some st1 ->
        begin
          let ost = app_map_lookup trans.app (st1, ost2) in
          match ost with
          | Some st ->
            (trans, Some st)
          | None ->
            begin
              (
                { fvar = trans.fvar
                ; app = app_map_insert trans.app (st1, ost2) trans.next_state
                ; next_state = trans.next_state + 1
                ; state_to_a = trans.state_to_a
                },
                Some (trans.next_state)
              )
            end
        end
      | None -> fail "BottomUp.add_term_aux: function doesn't have a state"
    end
  | _ -> (trans, None)

val add_term: #a:Type0 -> net a -> term -> a -> Tac (net a)
let add_term #a trans t x =
  match add_term_aux trans t with
  | (trans, Some st) ->
    begin
      //print ((nat_to_string st) ^ "\n");
      { fvar = trans.fvar
      ; app = trans.app
      ; next_state = trans.next_state
      ; state_to_a =
        match map_lookup trans.state_to_a st with
        | Some l -> map_insert trans.state_to_a st (x::l)
        | None -> map_insert trans.state_to_a st [x]
      }
    end
  | (_, None) -> fail "BottomUp.add_term: add_term_aux didn't return a Some"

val match_term: #a:Type0 -> net a -> term -> Tac (list a)
let match_term #a trans t =
  let sts = term_to_state trans t in
  //print ((join_strings ", " (List.Tot.map nat_to_string sts)) ^ "\n");
  List.Tot.fold_right (fun st acc ->
    match map_lookup trans.state_to_a st with
    | Some l -> l@acc
    | None -> acc
  ) sts []

let merge_net #a x y = fail "BottomUp.merge: not implemented"

