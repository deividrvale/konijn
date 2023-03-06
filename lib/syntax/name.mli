(** This module exports a module type {!module-type:NAME}, which is an abstract interface for {b names}, and one module {!module:IndexedName} of type {!module-type:NAME}.
*)

module type NAME = sig
    type t
    (** [t] is the type for {b names}. *)

    val equal : t -> t -> bool
    (** [equal t t'] is whether the names [t] and [t'] are structural equal. *)

    val register : string -> t
    (** [register name] is the name (of type {!type:t}) registered with key [name].
    If there is already a name registered with this key,
    then [register_name name] returns the already registered name associated
    with this key.
    This behavior make this module behave as a 'set-like' structure. *)

    val gen_name : unit -> t
    (** [gen_name ()] generates a new fresh name of type [t]. *)

    val compare : t -> t -> int
    (** [compare x y] returns [0] if [x] is equal to [y],
        a negative integer if [x] is less than [y],
        and a positive integer if [x] is greater than [y].

        {b Note:} [compare] enforces a total order over the type {!type:t}.
    *)

    val to_string : t -> string
    (** [to_string name] is the string representation of the name [name].

    {b Note:} a standard implementation of [to_string] would return the
    same string used as key for registering [name].
    Hence, satisfying
    [to_string (get_symb (register_name "n"))]
    equals ["n"].
    This property is not enforced, however.
    It is up to implementers the choice of how to write names back to string format.
    *)

    val of_string : string -> t
    (** [of_string name] returns the symbol registered with [name].
    @raise Name_Not_found if there is no such name. *)

    val of_string_opt : string -> t option
    (** [of_string_opt name] is [Some t] if there is a symbol [t] registered with [name], [None] otherwise. *)

    val name_list : unit -> t list
    (** [symb_list ()] is the list of all names registered up to calling this function. *)

    exception Name_Not_found of string
    (** Raised whenever calling [get_symb]. *)
end

(** Interface for {b names}.
    It can be used to represent base types, variables, and function symbols.*)

module IndexedNames : functor () -> NAME
