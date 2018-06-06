(* -------------------------------------------------------------------- *)
let rec sum i =
  if i <= 0 then 0 else i + sum (i - 1)

let rec sum_sq i =
  if i <= 0 then 0 else i * i + sum (i - 1)

let sum_gen f =
  let rec doit i =
    if i <= 0 then 0 else f i + doit (i - 1)
  in fun i -> doit i

let sum    = sum_gen (fun x -> x)
let sum_eq = sum_gen (fun x -> x * x)

(* -------------------------------------------------------------------- *)
let dicho f (a, b) e =
  let isincr = f a <= f b in

  let rec aux (a, b) : float =
    let delta = b -. a in
    let mid   = a +. delta /. 2. in

    if delta < e then mid else

    let fm_normed = f mid *. (if isincr then 1. else -1.) in

    aux (if fm_normed < 0. then (mid, b) else (a, mid))

  in aux (a, b)

(* -------------------------------------------------------------------- *)
module Utils = struct
  let is_none =
    function None -> true | _ -> false

  let is_some =
    function Some _ -> true | _ -> false

  let oget (x0 : 'a) =
    function None -> x0 | Some v -> v

  let oiter (f : 'a -> unit) =
    function None -> () | Some v -> f v

  let omap (f : 'a -> 'b) =
    function None -> None | Some v -> Some (f v)

  let obind (f : 'a -> 'b option) =
    function None -> None | Some v -> f v
end

(* -------------------------------------------------------------------- *)
let iofold (f : string -> 'b -> 'b) (fname : string) (x : 'b) =
  let x      = ref x in
  let stream = open_in fname in

  try
    try
      while true do x := f (input_line stream) !x done; assert false
    with End_of_file -> close_in stream; !x
  with e -> close_in stream; raise e

(* -------------------------------------------------------------------- *)
module Queue : sig
  type 'a queue
end = struct
  type 'a queue = 'a list * 'a list

  let empty : 'a queue =
    ([], [])

  let is_empty (q : 'a queue) =
    match q with ([], []) -> true | _ -> false

  let push (x : 'a) ((s1, s2) : 'a queue) =
    (x :: s1, s2)

  let rec pull (q : 'a queue) =
    match q with
    | [], []      -> None
    | s1, x :: s2 -> Some (x, (s1, s2))
    | s1, []      -> pull ([], List.rev s1)
end

(* -------------------------------------------------------------------- *)
module PArray : sig
  type 'a parray

  val make       : int -> 'a -> 'a parray
  val norm       : 'a parray -> unit
  val get        : 'a parray -> int -> 'a
  val set        : 'a parray -> int -> 'a -> 'a parray
  val length     : 'a parray -> int
  val to_list    : 'a parray -> 'a list
  val iter       : ('a -> unit) -> 'a parray -> unit
  val iteri      : (int -> 'a -> unit) -> 'a parray -> unit
  val fold_left  : ('b -> 'a -> 'b) -> 'b -> 'a parray -> 'b
  val fold_right : ('a -> 'b -> 'b) -> 'a parray -> 'b -> 'b
  val for_all    : ('a -> bool) -> 'a parray -> bool
end = struct
  type 'a parray =
    'a data ref

  and 'a data =
    | Array of 'a array
    | Delta of int * 'a * 'a parray

  let asarray (a : 'a data) =
    match a with Array a -> a | _ -> assert false

  let make (n : int) (x : 'a) =
    ref (Array (Array.make n x))

  let setget (a : 'a array) (i : int) (v : 'a)  =
    let v' = a.(i) in a.(i) <- v; v'

  let rec norm_r (a : 'a parray) =
    match !a with
    | Array a ->
        a        
    | Delta (i, v, suba) ->
        let subr = norm_r suba in
        let v'   = setget subr i v in
        a := !suba; suba := Delta (i, v', a); subr

  let norm (a : 'a parray) = ignore (norm_r a)

  let get (a : 'a parray) (i : int) =
    (norm_r a).(i)

  let set (a : 'a parray) (i : int) (v : 'a) =
    let r = norm_r a in
    let o = r.(i) in

    if v == o then a else begin
      let aout = ref !a in
      r.(i) <- v; a := Delta (i, o, aout); aout
    end

  let lift (f : 'a array -> 'b) (a : 'a parray) =
    f (norm_r a)

  let length (a : 'a parray) =
    lift Array.length a

  let to_list (a : 'a parray) =
    lift Array.to_list a

  let iter (f : 'a -> unit) (a : 'a parray) =
    lift (Array.iter f) a

  let iteri (f : int -> 'a -> unit) (a : 'a parray) =
    lift (Array.iteri f) a

  let fold_left (f : 'b -> 'a -> 'b) (x : 'b) (a : 'a parray) =
    lift (Array.fold_left f x) a

  let fold_right (f : 'a -> 'b -> 'b) (a : 'a parray) (x : 'b) =
    lift (fun a -> Array.fold_right f a x) a

  let for_all (f : 'a -> bool) (a : 'a parray) =
    lift (Array.for_all f) a
end

(* -------------------------------------------------------------------- *)
module T9 : sig
  type t9

  exception InvalidKey  of int
  exception InvalidChar of char

  val empty  : t9
  val insert : string -> t9 -> t9
  val remove : string -> t9 -> t9
  val search : int list -> t9 -> string list

  val key_of_char : char -> int
end = struct
  type t9 = {
    words    : string list;
    children : (t9 option) PArray.parray;
  }

  exception InvalidKey  of int
  exception InvalidChar of char

  let key_of_char (c : char) =
    match c with
    | 'a' | 'b' | 'c'       -> 2
    | 'd' | 'e' | 'f'       -> 3
    | 'g' | 'h' | 'i'       -> 4
    | 'j' | 'k' | 'l'       -> 5
    | 'm' | 'n' | 'o'       -> 6
    | 'p' | 'q' | 'r' | 's' -> 7
    | 't' | 'u' | 'v'       -> 8
    | 'w' | 'x' | 'y' | 'z' -> 9

    | _ -> raise (InvalidChar c)

  let index_of_key (i : int) =
    if 2 <= i && i <= 9 then i - 2 else raise (InvalidKey i)

  let empty : t9 =
    { words = []; children = PArray.make 8 None; }

  let is_empty = function
    | { words = []; children } ->
        PArray.for_all Utils.is_none children
    | _ -> false

  let update_child_at (t : t9) (i : int) (sub : t9 option) =
    { t with children = PArray.set t.children i sub }

  let insert_at_root (s : string) =
    let rec aux = function
      | []                 -> [s]
      | w :: ws when s > w -> w :: aux ws
      | w :: ws when s = w -> ws
      | _ :: _  as   ws    -> s :: ws

    in fun t -> { t with words = aux t.words }

  let remove_at_root (s : string) (t : t9) =
    { t with words = List.filter ((=) s) t.words }

  let insert (s : string) =
    let rec aux (i : int) (t : t9) : t9 =
      if i >= String.length s then insert_at_root s t else
        let idx = index_of_key (key_of_char s.[i]) in
        let sub = Utils.oget empty (PArray.get t.children idx) in
        let sub = aux (i+1) sub in
        update_child_at t idx (Some sub)
    in fun t -> aux 0 t

  let remove_r (s : string) =
    let rec aux (i : int) (t : t9) : t9 option =
      let res =
        if i >= String.length s then
          remove_at_root s t
        else
          let idx = index_of_key (key_of_char s.[i]) in
          let sub = PArray.get t.children idx in
          let sub = Utils.obind (aux (i+1)) sub in
          update_child_at t idx sub
      in if is_empty res then None else Some res
    in fun t -> aux 0 t

  let remove (s : string) (t : t9) =
    Utils.oget empty (remove_r s t)

  let search (d : int list) (t : t9) : string list =
    let rec aux (d : int list) (t : t9 option) =
      match d, t with
      | _ , None ->
          []
      | [], Some { words } ->
          words
      | i :: d, Some { children } ->
          aux d (PArray.get children (index_of_key i))
    in aux d (Some t)
end

(* -------------------------------------------------------------------- *)
module Future : sig
  type 'a future

  val offun : (unit -> 'a) -> 'a future
  val ofval : 'a -> 'a future
  val force : 'a future -> 'a
end = struct
  type 'a future_ = Future of (unit -> 'a) | Value of 'a
  type 'a future  = 'a future_ ref

  let offun (f : unit -> 'a) =
    ref (Future f)

  let ofval (x : 'a) =
    ref (Value x)

  let force (v : 'a future) =
    match !v with
    | Value  x -> x
    | Future f -> let x = f () in v := Value x; x
end

type 'a future = 'a Future.future

(* -------------------------------------------------------------------- *)
module WList : sig
  type 'a wlist

  val nil     : 'a wlist
  val cons    : 'a -> (unit -> 'a wlist) -> 'a wlist
  val const   : 'a -> 'a wlist
  val iter    : ('a -> 'a) -> 'a -> 'a wlist
  val oflist  : 'a list -> 'a wlist
  val observe : 'a wlist -> ('a * (unit -> 'a wlist)) option
  val filter  : ('a -> bool) -> 'a wlist -> 'a wlist
  val map     : ('a -> 'b) -> 'a wlist -> 'b wlist
  val zip     : 'a wlist -> 'b wlist -> ('a * 'b) wlist
  val drop    : int -> 'a wlist -> 'a wlist
  val fold    : (int -> 'a -> 'b -> 'b) -> 'a wlist -> int -> 'b -> 'b
end = struct
  type 'a wlist = Nil | Cons of 'a * (unit -> 'a wlist)

  let nil : 'a wlist =
    Nil

  let cons (x : 'a) (s : unit -> 'a wlist) =
    Cons (x, s)

  let rec const (x : 'a) =
    cons x (fun () -> const x)

  let rec iter (f : 'a -> 'a) (x : 'a) =
    cons x (fun () -> iter f (f x))

  let rec oflist (s : 'a list) =
    match s with
    | [] -> Nil
    | x :: s -> cons x (fun () -> oflist s)

  let observe (s : 'a wlist) =
    match s with
    | Nil -> None
    | Cons (x, s) -> Some (x, s)

  let filter (p : 'a -> bool) =
    let rec aux (s : 'a wlist) =
      match s with
      | Nil -> nil
      | Cons (x, s) when p x ->
          cons x (fun () -> aux (s ()))
      | Cons (_, s) ->
          aux (s ())
    in fun s -> aux s

  let map (f : 'a -> 'b) =
    let rec aux (s : 'a wlist) =
      match s with
      | Nil -> nil
      | Cons (x, s) -> cons (f x) (fun () -> aux (s ()))
    in fun s -> aux s

  let rec zip (s1 : 'a wlist) (s2 : 'b wlist) =
    match s1, s2 with
    | Cons (x1, s1), Cons (x2, s2) ->
        cons (x1, x2) (fun () -> zip (s1 ()) (s2 ()))
    | _, _ ->
        nil

  let rec drop (i : int) (s : 'a wlist) =
    if i <= 0 then s else
      match s with
      | Nil -> nil
      | Cons (_, s) -> drop (i-1) (s ())

  let fold f (s : 'a wlist) (i : int) =
    let rec aux (s : 'a wlist) (j : int) (x : 'b) =
      if 0 <= i && i = j then x else
        match s with
        | Nil -> x
        | Cons (y, s) -> aux (s ()) (j+1) (f j y x)
    in fun x -> aux s 0 x
end

(* -------------------------------------------------------------------- *)
let fibonacci n =
  if n < 0 then 0 else

  let mem =
    Array.init (n+1) (fun i -> if i < 2 then 1 else -1)
  in

  let rec aux n =
    if mem.(n) >= 0 then mem.(n) else
      let v = aux (n-1) + aux (n-2) in
      mem.(n) <- v; v
  in aux n

(* -------------------------------------------------------------------- *)
let knapsack (vps : (int * int) array) (c : int) =
  assert (Array.for_all (fun (v, p) -> 0 <= v && 0 <= 0) vps);
  assert (0 <= c);

  let rec aux (i : int) (j : int) =
    if i = 0 then 0 else

    let (v, p) = vps.(i-1) in

    if p <= j then
      max (aux (i-1) j) (aux (i-1) (j - p) + v)
    else
      aux (i-1) j

  in aux (Array.length vps) c

(* -------------------------------------------------------------------- *)
let knapsack_mem (vps : (int * int) array) (c : int) =
  assert (Array.for_all (fun (v, p) -> 0 <= v && 0 <= 0) vps);
  assert (0 <= c);

  let mem = Hashtbl.create (c * Array.length vps) in

  let rec aux (i : int) (j : int) =
    try  Hashtbl.find mem (i, j)
    with Not_found ->

    let v =
      if i = 0 then 0 else

      let (v, p) = vps.(i-1) in

      if p <= j then
        max (aux (i-1) j) (aux (i-1) (j - p) + v)
      else
        aux (i-1) j
    in Hashtbl.add mem (i, j) v; v

  in aux (Array.length vps) c
