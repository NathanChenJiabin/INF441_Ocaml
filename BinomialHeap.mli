
(* Binomial heap *)

type 'a heap

val empty : 'a heap

val is_empty : 'a heap -> bool

val insert : 'a heap -> int -> 'a -> 'a heap

val find_min : 'a heap -> 'a

val merge : 'a heap -> 'a heap -> 'a heap

val extract_min : 'a heap -> 'a * 'a heap

val extract_minp : 'a heap -> (int * 'a) * 'a heap
