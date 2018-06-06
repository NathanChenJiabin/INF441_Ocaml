
(* Binomial tree *)

type 'a tree

val key : 'a tree -> int

val value : 'a tree -> 'a

val children : 'a tree -> 'a tree list

val rank : 'a tree -> int

val node : int -> 'a -> 'a tree
  (* build a leaf i.e. a tree of order 0 *)

val link : 'a tree -> 'a tree -> 'a tree
  (* build a tree of order k given two trees of rank k,
     while preserving the heap structure *)

val iter : ('a -> 'b) -> 'a tree -> unit
