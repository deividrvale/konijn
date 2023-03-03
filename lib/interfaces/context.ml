open Base_modules

module type TY_CTX = sig
  exception Not_found_in_Ctx of string

  type exp
  type t

  val weaken : exp -> t -> unit

  val remove : exp -> unit

  val type_of : exp -> t option

end
