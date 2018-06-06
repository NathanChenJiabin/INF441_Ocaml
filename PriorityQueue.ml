
(** A simple wrapper around BinomialHeap, using a reference *)

module BH = BinomialHeap

type 'a t = 'a BH.heap ref

let create () =
  ref BH.empty

let is_empty q =
  BH.is_empty !q

let push q n x =
  q := BH.insert !q n x

let pop q =
  let x, q' = BH.extract_minp !q in
  q := q';
  x

(** tests *)

let () =
  let q = create () in
  push q 2 "a";
  push q 1 "b";
  assert (pop q = (1, "b"));
  assert (pop q = (2, "a"));
  assert (is_empty q)


