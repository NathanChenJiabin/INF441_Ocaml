
(* Binomial tree *)

type 'a tree = {
       key: int;
     value: 'a;
  children: 'a tree list;
      rank: int; (* = List.length children *)
}

let node key value =
  { key = key; value = value; children = []; rank = 0 }

let rank t =
  t.rank

let key t =
  t.key

let value t =
  t.value

let children t =
  t.children

let rec link t1 t2 =
  assert (rank t1 = rank t2);
  if key t2 >= key t1 then
    { key = t1.key;
      value = t1.value;
      children = t2 :: t1.children;
      rank = t1.rank + 1 }
  else
    link t2 t1

let rec iter f t =
  f (value t);
  List.iter (iter f) (children t)

(* tests *)

let rec size t =
  1 + size_list (children t)

and size_list = function
  | [] -> 0
  | t :: ts -> size t + size_list ts

let () =
  let zero = node 0 "a" in
  let one = link zero zero in
  let two = link one one in
  assert (size two = 4);
  assert (rank two = 2)

