module LCF.Net.BottomUp

open FStar.Tactics
open LCF.Util

// TODO: more efficient associative datastructure
noeq type net (a:Type0) =
  {
    fvar: list (fv & nat);
    app: list ((nat & (option nat)) & nat);
    next_state: nat;
    state_to_a: list (nat & a)
  }

val empty_net: #a:Type0 -> net a
let empty_net #a =
  { fvar = []
  ; app = []
  ; next_state = 0
  ; state_to_a = []
  }

val term_to_state: #a:Type0 -> net a -> term -> Tac (list nat)
let rec term_to_state #a trans t =
  match (inspect t) with
  | Tv_FVar fv ->
    begin
      Tactics.Util.fold_right (fun (fv2, st) acc -> if fv_eq fv fv2 then st::acc else acc) (trans.fvar) []
    end
  | Tv_App hd argv ->
    begin
      let sts1 = term_to_state trans hd in
      let sts2 = term_to_state trans (fst argv) in
      Tactics.Util.fold_right (fun ((st1, ost2), str) acc ->
        let ok (ost:option nat) (sts:list nat) =
          match ost with
          | Some st -> List.Tot.mem #nat st sts
          | None -> true
        in
        let ok1 = List.Tot.mem #nat st1 sts1 in //ok ost1 sts1 in
        let ok2 = ok ost2 sts2 in
        if ok1 && ok2 then str::acc
        else acc
      ) (trans.app) []
    end
  | _ -> []

val add_term_aux: #a:Type0 -> net a -> term -> Tac (net a & option nat)
let rec add_term_aux #a trans t =
  match inspect t with
  | Tv_FVar fv ->
    begin
      let t_state = term_to_state trans t in
      match t_state with
      | [] ->
        (
          { fvar = (fv, trans.next_state)::trans.fvar
          ; app = trans.app
          ; next_state = trans.next_state+1
          ; state_to_a = trans.state_to_a
          },
          Some (trans.next_state)
        )
      | [st] -> (trans, Some st)
      | _ -> fail "BottomUp.add_term_aux: too many states for free variable"
    end
  | Tv_App hd argv ->
    begin
      let (trans, ost1) = add_term_aux trans hd in
      let (trans, ost2) = add_term_aux trans (fst argv) in
      match ost1 with
      | Some st1 ->
        begin
          let ost = List.Tot.assoc (st1, ost2) trans.app in
          match ost with
          | Some st ->
            (trans, Some st)
          | None ->
            begin
              (
                { fvar = trans.fvar
                ; app = ((st1, ost2), trans.next_state)::trans.app
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
      ; state_to_a = (st,x)::(trans.state_to_a)
      }
    end
  | (_, None) -> fail "BottomUp.add_term: add_term_aux didn't return a Some"

val match_term: #a:Type0 -> net a -> term -> Tac (list a)
let match_term #a trans t =
  let sts = term_to_state trans t in
  //print ((join_strings ", " (List.Tot.map nat_to_string sts)) ^ "\n");
  List.Tot.fold_right (fun st acc ->
    List.Tot.fold_right (fun (stx, x) acc2 ->
      if st = stx then x::acc2 else acc2
    ) trans.state_to_a acc
  ) sts []

let merge_net #a x y = fail "BottomUp.merge: not implemented"

