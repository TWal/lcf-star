module LCF.Map

(*** Datatypes and invariants ***)

type ordering =
  | Lt
  | Eq
  | Gt

type cmp_on_ (a:Type0) =
  a -> a -> ordering

type map_ (a:Type0) (cmp:cmp_on_ a) (b:Type) =
  | Nil: map_ a cmp b
  | Node: bf:int{-1 <= bf && bf <= 1} -> left:map_ a cmp b -> (a&b) -> right:map_ a cmp b -> map_ a cmp b

val cmp_on_axioms: #a:Type0 -> cmp_on_ a -> Type0
let cmp_on_axioms #a cmp =
  ( //Reflexivity
    forall a. cmp a a == Eq
  ) /\ ( //Anti-symetry
    forall a b.
    (cmp a b == Lt ==> cmp b a == Gt) /\
    (cmp a b == Eq ==> cmp b a == Eq) /\
    (cmp a b == Gt ==> cmp b a == Lt)
  ) /\ ( //Transitivity
    forall a b c.
    (cmp a b == Lt /\ cmp b c == Lt ==> cmp a c == Lt) /\
    (cmp a b == Lt /\ cmp b c == Eq ==> cmp a c == Lt) /\
    (cmp a b == Eq /\ cmp b c == Lt ==> cmp a c == Lt) /\
    (cmp a b == Eq /\ cmp b c == Eq ==> cmp a c == Eq) /\
    (cmp a b == Eq /\ cmp b c == Gt ==> cmp a c == Gt) /\
    (cmp a b == Gt /\ cmp b c == Eq ==> cmp a c == Gt) /\
    (cmp a b == Gt /\ cmp b c == Gt ==> cmp a c == Gt)
  )

val max: int -> int -> int
let max a b = if a < b then b else a

val height: #a:Type0 -> #cmp:cmp_on_ a -> #b:Type -> map_ a cmp b -> GTot nat
let rec height #a #cmp #b m =
  match m with
  | Nil -> 0
  | Node _ l _ r -> (max (height l) (height r)) + 1

val bf_invariant: #a:Type0 -> #cmp:cmp_on_ a -> #b:Type -> map_ a cmp b -> Type0
let rec bf_invariant #a #cmp #b m =
  match m with
  | Nil -> True
  | Node bf l _ r -> (bf == (height r) - (height l)) /\ bf_invariant l /\ bf_invariant r

val in_map: #a:Type0 -> #cmp:cmp_on_ a -> #b:Type -> map_ a cmp b -> a -> Type0
let rec in_map #a #cmp #b m x0 =
  match m with
  | Nil -> False
  | Node _ l (x,y) r -> (in_map l x0) \/ (cmp x0 x == Eq) \/ (in_map r x0)

val bst_invariant: #a:Type0 -> #cmp:cmp_on_ a -> #b:Type -> map_ a cmp b -> Type0
let rec bst_invariant #a #cmp #b m =
  match m with
  | Nil -> True
  | Node _ l (x,y) r ->
    (forall xl. in_map l xl ==> cmp xl x == Lt) /\
    (forall xr. in_map r xr ==> cmp x xr == Lt) /\
    (bst_invariant l /\ bst_invariant r)

type cmp_on (a:Type0) = cmp:cmp_on_ a{cmp_on_axioms cmp}
type map (a:Type0) (cmp:cmp_on a) (b:Type) = m:map_ a cmp b{bf_invariant m /\ bst_invariant m}

(*** Helper functions for `cmp_on` ***)

val cmp_on_lex: #a:Type0 -> #b:Type0 -> cmp_on a -> cmp_on b -> cmp_on (a&b)
let cmp_on_lex #a #b cmpa cmpb (xa,xb) (ya,yb) =
  match cmpa xa ya with
  | Lt -> Lt
  | Gt -> Gt
  | Eq -> cmpb xb yb

val cmp_on_option: #a:Type0 -> cmp_on a -> cmp_on (option a)
let cmp_on_option #a cmp ox oy =
  match ox, oy with
  | None, None -> Eq
  | Some x, None -> Gt
  | None, Some y -> Lt
  | Some x, Some y -> cmp x y

val cmp_on_list_leq_n: #n:nat -> #a:Type0 -> cmp_on a -> cmp_on (l:list a{List.Tot.length l <= n})
let rec cmp_on_list_leq_n #n #a cmp (lx:(l:list a{List.Tot.length l <= n})) (ly:(l:list a{List.Tot.length l <= n})) =
  match lx, ly with
  | [], [] -> Eq
  | x::xs, [] -> Gt
  | [], y::ys -> Lt
  | x::xs, y::ys ->
    begin
      cmp_on_lex cmp (cmp_on_list_leq_n #(n-1) cmp) (x,xs) (y,ys)
    end

val cmp_on_list_: #a:Type0 -> cmp_on a -> list a -> list a -> ordering
let rec cmp_on_list_ #a cmp lx ly =
  match lx, ly with
  | [], [] -> Eq
  | x::xs, [] -> Gt
  | [], y::ys -> Lt
  | x::xs, y::ys ->
    begin
      match cmp x y with
      | Lt -> Lt
      | Gt -> Gt
      | Eq -> cmp_on_list_ cmp xs ys
    end

//If you find a prettier way to define this function, I would happily buy you a beer!
val cmp_on_list: #a:Type0 -> cmp_on a -> cmp_on (list a)
let cmp_on_list #a cmp =
  let rec cmp_on_list_eq_cmp_on_list_leq_n (#a:Type0) (cmp:cmp_on a) (n:nat) (lx:list a) (ly:list a): Lemma
    ((List.Tot.length lx <= n /\ List.Tot.length ly <= n) ==> cmp_on_list_ cmp lx ly == cmp_on_list_leq_n #n cmp lx ly) =
    match lx,ly with
    | x::xs, y::ys -> if (n <= 0) then () else cmp_on_list_eq_cmp_on_list_leq_n cmp (n-1) xs ys
    | _ -> ()
  in
  FStar.Classical.forall_intro_3 (cmp_on_list_eq_cmp_on_list_leq_n #a cmp);
  assert (forall (lx:list a) (ly:list a).
    let n = max (List.Tot.length lx) (List.Tot.length ly) in
    cmp_on_list_ cmp lx ly == cmp_on_list_leq_n #n cmp lx ly
  );
  //The following assert can be removed, but I don't understand how?
  assert (forall (lx:list a) (ly:list a) (lz:list a).
    let n = max (max (List.Tot.length lx) (List.Tot.length ly)) (List.Tot.length lz) in
    cmp_on_list_ cmp lx ly == cmp_on_list_leq_n #n cmp lx ly /\
    cmp_on_list_ cmp lx lz == cmp_on_list_leq_n #n cmp lx lz /\
    cmp_on_list_ cmp ly lz == cmp_on_list_leq_n #n cmp ly lz
  );
  cmp_on_list_ cmp

(*** Map definition ***)

val map_empty: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> map a cmp b
let map_empty #a #cmp #b =
  Nil

val map_is_empty: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> map a cmp b -> bool
let map_is_empty #a #cmp #b m =
  match m with
  | Nil -> true
  | _ -> false

val map_lookup: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> m:map a cmp b -> x0:a -> Pure (option b)
  (requires True)
  (ensures fun res -> (Some? res) <==> in_map m x0)
let rec map_lookup #a #cmp #b m x0 =
  match m with
  | Nil -> None
  | Node bf l (x,y) r ->
    begin
      match cmp x0 x with
      | Lt -> map_lookup l x0
      | Eq -> Some y
      | Gt -> map_lookup r x0
    end

#push-options "--z3rlimit 30"
val rotate_right: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> l:map a cmp b -> x:(a&b) -> r:map a cmp b -> Pure (map a cmp b & bool)
  (requires
    (height r) - (height l) == -2 /\
    (forall xl. in_map l xl ==> cmp xl (fst x) == Lt) /\ (forall xr. in_map r xr ==> cmp (fst x) xr == Lt)
  )
  (ensures fun (res, height_unchanged) ->
    height res == (max (height l) (height r)) + 1 + (if height_unchanged then 0 else -1) /\
    (forall x0. in_map res x0 <==> (in_map l x0) \/ (cmp x0 (fst x) == Eq) \/ (in_map r x0))
  )
let rotate_right #a #cmp #b l x r =
  match l with
  | Node lbf ll lx lr ->
    begin
      if lbf = -1 then
        (Node 0 ll lx (Node 0 lr x r) , false)
      else if lbf = 0 then
        (Node 1 ll lx (Node (-1) lr x r), true)
      else (
        match lr with
        | Node lrbf lrl lrx lrr ->
          begin
            let b1 = if lrbf = 1 then -1 else 0 in
            let b2 = if lrbf = -1 then 1 else 0 in
            (Node 0 (Node b1 ll lx lrl) lrx (Node b2 lrr x r), false)
          end
      )
    end
#pop-options

#push-options "--z3rlimit 30"
val rotate_left: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> l:map a cmp b -> x:(a&b) -> r:map a cmp b -> Pure (map a cmp b & bool)
  (requires
    (height r) - (height l) == 2 /\
    (forall xl. in_map l xl ==> cmp xl (fst x) == Lt) /\ (forall xr. in_map r xr ==> cmp (fst x) xr == Lt)
  )
  (ensures fun (res, height_unchanged) ->
    height res == (max (height l) (height r)) + 1 + (if height_unchanged then 0 else -1) /\
    (forall x0. in_map res x0 <==> (in_map l x0) \/ (cmp x0 (fst x) == Eq) \/ (in_map r x0))
  )
let rotate_left #a #cmp #b l x r =
  match r with
  | Node rbf rl rx rr ->
    begin
      if rbf = 1 then
        (Node 0 (Node 0 l x rl) rx rr, false)
      else if rbf = 0 then
        (Node (-1) (Node 1 l x rl) rx rr, true)
      else
        match rl with
        | Node rlbf rll rlx rlr ->
          begin
            let b1 = if rlbf = 1 then -1 else 0 in
            let b2 = if rlbf = -1 then 1 else 0 in
            (Node 0 (Node b1 l x rll) rlx (Node b2 rlr rx rr), false)
          end
    end
#pop-options

#push-options "--z3rlimit 30"
val map_insert_aux: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> m:map a cmp b -> x0:a -> b -> Pure (map a cmp b & bool)
  (requires True)
  (ensures fun (res, height_increased) ->
    height res = (height m) + (if height_increased then 1 else 0) /\
    (forall x. in_map res x <==> (in_map m x \/ cmp x0 x == Eq))
  )
let rec map_insert_aux #a #cmp #b m x0 y0 =
  match m with
  | Nil -> (Node 0 Nil (x0, y0) Nil, true)
  | Node bf l (x,y) r ->
    begin
      match cmp x0 x with
      | Lt ->
        begin
          let (l_new, height_increased) = map_insert_aux l x0 y0 in
          if height_increased then (
            if bf = -1 then (
              rotate_right l_new (x,y) r
            )
            else if bf = 0 then
              (Node (-1) l_new (x,y) r, true)
            else
              (Node 0 l_new (x,y) r, false)
          ) else (
            (Node bf l_new (x,y) r, false)
          )
        end
      | Eq -> (Node bf l (x0,y0) r, false)
      | Gt ->
        begin
          let (r_new, height_increased) = map_insert_aux r x0 y0 in
          if height_increased then (
            if bf = -1 then
              (Node 0 l (x,y) r_new, false)
            else if bf = 0 then
              (Node 1 l (x,y) r_new, true)
            else
              rotate_left l (x,y) r_new
          ) else (
            (Node bf l (x,y) r_new, false)
          )
        end
    end
#pop-options

val map_insert: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> m:map a cmp b -> x0:a -> b -> Pure (map a cmp b)
  (requires True)
  (ensures fun res -> forall x. in_map res x <==> (in_map m x \/ cmp x0 x == Eq))
let map_insert #a #cmp #b m x0 y0 =
  fst (map_insert_aux m x0 y0)
