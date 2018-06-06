
(* Binomial heap. *)

module BT = BinomialTree

type 'a heap = 'a BT.tree list
  (* list of heap-ordered, binomial trees, with increasing orders *)

let empty =
  []

let is_empty h =
  h = []

let rec add_tree h t =
  match h with
  | [] ->
      [t]
  | ht :: h as b ->
      let rht = BT.rank ht in
      let rt = BT.rank t in
      if rt < rht then
        t :: b
      else if rt = rht then
        add_tree h (BT.link ht t)
      else
        ht :: add_tree h t

let insert h k v =
  add_tree h (BT.node k v)

(* The node with minimum key in a binomial tree is the root of the tree.
   The node with minimum key in a binomial heap, which is a list of
   binomial trees, is found by iterating over the list of trees,
   examining just the roots, and keeping the element with minimum key. *)

exception Empty

let find_min h =
  match h with
  | [] ->
      raise Empty
  | t :: h ->
      let rec aux (k, v) = function
      | [] ->
          v
      | t :: h ->
          let k' = BT.key t in
          if k' <= k then aux (k', BT.value t) h
          else aux (k, v) h
     in
     aux (BT.key t, BT.value t) h

(* tests *)

let () =
  let h = empty in
  let h = insert h 5 "a" in
  assert (find_min h = "a");
  let h = insert h 8 "b" in
  assert (find_min h = "a");
  let h = insert h 2 "c" in
  assert (find_min h = "c");
  let h = insert h 2 "d" in
  assert (find_min h = "c");
  let h = insert h 2 "e" in
  assert (find_min h = "c")

(* Merging two binomial heaps *)

(* Similar to binary addition (see Binary.add)

   One simple solution is to insert the trees of h2 into h1 one by one *)
let rec merge h1 h2 =
  match h2 with
  | []        -> h1
  | ht2 :: h2 -> merge (add_tree h1 ht2) h2

(* But we can also do it more efficiently (as for Binary.add) by
   exploiting the fact that the two lists are sorted *)
let rec merge h1 h2 = match h1, h2 with
  | [], _ -> h2
  | _, [] -> h1
  | hd1 :: tl1, hd2 :: tl2 ->
      if BT.rank hd1 < BT.rank hd2 then
        hd1 :: merge tl1 h2
      else if BT.rank hd2 < BT.rank hd1 then
        hd2 :: merge h1 tl2
      else
        add_tree (merge tl1 tl2) (BT.link hd1 hd2)

(* Smallest element *)

let rec extract_min_tree = function
  | [] -> raise Empty
  | [t] -> t, []
  | t :: h ->
      let t', h' = extract_min_tree h in
      if BT.key t < BT.key t' then
        t, h
      else
        t', t :: h'

let extract_min h =
  let t, h = extract_min_tree h in
  BT.value t, merge (List.rev (BT.children t)) h

let extract_minp h =
  let t, h = extract_min_tree h in
  (BT.key t, BT.value t), merge (List.rev (BT.children t)) h

(* tests *)

let () =
  let h = empty in
  let h = insert h 1 "a" in
  let h = insert h 1 "b" in
  assert (fst (extract_min h) = "a");
  let h = insert h 1 "c" in
  let x, h = extract_min h in
  assert (x = "a");
  let x, h = extract_min h in
  assert (x = "b");
  let x, h = extract_min h in
  assert (x = "c");
  ()

let rec to_sorted_list = function
  | [] -> []
  | h ->
     let x, h = extract_min h in
     x :: to_sorted_list h

let iter f h =
  List.iter (BT.iter f) h

let mem h x =
  let ans = ref false in
  iter (fun y -> ans := !ans || y = x) h;
  !ans
