
module type TOT = sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val to_string : t -> string
end

module type ATOM = sig
  include TOT
  val fresh : unit -> t
end

module AtomicNames
  (N : sig val atom_names : string end) : ATOM = struct
  type t = int
  let compare = Int.compare
  let equal = Int.equal
  let to_string a = N.atom_names ^ Int.to_string a
  let a : int ref = ref 0
  let fresh () =
    a := !a + 1;
    !a
end
