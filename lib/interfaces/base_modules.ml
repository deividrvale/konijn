
module type TOT = sig
  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool
end
