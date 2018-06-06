
type binary = int list

let rec to_int (bits : binary) : int =
  match bits with
  | k :: rest -> 1 lsl k + to_int rest
  | []        -> 0
  (* The meaning of the list [k :: rest], whose first element is [k],
     is the sum of [2^k] and the meaning of the list [rest]. *)

let () =
  assert (to_int [0; 1; 4] = 19)

(* The auxiliary function [of_int_aux k n] converts the number [2^k * n]
   to a list of type [binary]. *)
let rec of_int_aux (k : int) (n : int) : binary =
  if n = 0 then
    (* [n] is [0], so the desired list of bits is empty. *)
    []
  else if n mod 2 = 1 then
    (* [n] is odd, so its binary representation ends with a 1 bit. Thus,
       the desired list of bits should begin with [k]. To compute the
       rest, we examine the remaining bits of [n] (given by [n / 2],
       which is the same as [(n - 1) / 2]) and we increment [k], so as
       to keep track of the weight of these bits. *)
    k :: of_int_aux (k + 1) (n / 2)
  else
    (* [n] is even. Same process, except the binary representation of [n]
       ends with a 0 bit, so we directly examine the remaining bits. *)
    of_int_aux (k + 1) (n / 2)

let of_int (n : int) : binary =
  of_int_aux 0 n

let () =
  assert (of_int 19 = [0; 1; 4])

let rec add_bit (n : binary) (k : int) : binary =
  match n with
  | [] ->
      [k]
  | k' :: l ->
      if k < k' then k :: n
      else if k' = k then add_bit l (k + 1)
      else k' :: add_bit l k

let () =
  assert (add_bit [0; 1; 4] 3 = [0; 1; 3; 4]);
  assert (add_bit [0; 1; 4] 5 = [0; 1; 4; 5]);
  assert (add_bit [0; 1; 4] 0 = [2; 4])

(* Addition *)

(* one can implement addition simply by adding the digits of n to m
   one at a time, using add_bit; the complexity is then O(len(m) * len(n)) *)
let rec add m n =
  match n with
  | []     -> m
  | k :: n -> add (add_bit m k) n

(* we can do it more efficiently, by using the fact that both lists
   are sorted; the complexity is then O(len(m) + len(n)) (though this
   is not obvious --- prove it as an exercise!) *)

let rec add m n = match m, n with
  | [], _ -> n
  | _, [] -> m
  | km :: rm, kn :: rn ->
    if km < kn then km :: add rm n
    else if kn < km then kn :: add m rn
    else add_bit (add rm rn) (km + 1)

(* tests *)

let () =
  let add_int x y = to_int (add (of_int x) (of_int y)) in
  assert (add_int 19 33 = 52);
  assert (add_int 41 29 = 70);
  assert (add_int 33 85 = 118)
