module LCF.Map

type cmp_on (a:Type0) =
  a -> a -> bool

type map (a:Type0) (cmp:cmp_on a) (b:Type) =
  list (a & b)

val map_empty: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> map a cmp b
let map_empty #a #cmp #b =
  []

val map_is_empty: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> map a cmp b -> bool
let map_is_empty #a #cmp #b m =
  match m with
  | [] -> true
  | _ -> false

val map_lookup: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> map a cmp b -> a -> option b
let map_lookup #a #cmp #b m x0 =
    List.Tot.fold_right (fun (x, y) acc -> if cmp x x0 then Some y else acc) m None

val map_insert: #a:Type0 -> #cmp:cmp_on a -> #b:Type -> map a cmp b -> a -> b -> map a cmp b
let map_insert #a #b m x y =
  (x,y)::m
