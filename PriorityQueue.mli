
(** Mutable priority queues
    (implemented using binomial heaps) *)

type 'a t

val create: unit -> 'a t

val is_empty: 'a t -> bool

val push: 'a t -> int -> 'a -> unit

val pop: 'a t -> int * 'a
