(*-----------------------------------------------------------------------------
  Abstract NAME symbols
-----------------------------------------------------------------------------*)

(** A functor implementing NAME should be used only for global level
  naming bookeeping.
  For instance, names for variables, function symbols, and so on.
  Local contexts should be implemented using the CTX type module
  provided in the Context module. *)

module type NAME = sig
  type t
  (** Abstract type for names. *)

  val equal : t -> t -> bool
  (** [equal t1 t2] is [true] iff [t1 == t2]. *)

  val register : string -> t
  (** [register x] registers the name [x] and return it as [t].
      If [x] is already registered, no new name is saved and [register x]
      returns the old name. *)

  (* val register_unit : string -> unit
  (** [register x] registers the name [x] and does not return it,
      for performance reasons. *) *)

  val gen_name : unit -> t
  (** [gen_name ()] generates a new fresh name of type [t]. *)

  val compare : t -> t -> int
  (**  *)

  val to_string : t -> string
  (** [to_string n] is a human-readable representation of [t]. *)

  val get_name : string -> t

  val get_name_opt : string -> t option

  val name_list : unit -> t list
  (** [name_list] returns the list of all registered names. *)

  exception Name_Not_found of string
  (** [Name_not_found] is raised whenever  *)
end

(*-----------------------------------------------------------------------------
  Names as indexed integers
-----------------------------------------------------------------------------*)

module IndexedNames () : NAME = struct
  exception Name_Not_found of string

  type t = int

  let equal = Int.equal

  let names = ref []
  (* [names] is reference pointer to the list of names at certain index
     it is initialized as the empty list *)

  let names_size = ref 0
  (* [idx_size] is the size of [names].
     Everytime a new name is registered, this number will be increased by one.*)

  let rec idx_of_name (name : string)
                      (name_lst : string list)
                      (idx : int)
                      : int =
    match name_lst with
    | [] -> idx
    | hd :: tl ->
      if String.equal name hd then
        idx
      else
        idx_of_name name tl (idx + 1)

  let get_name (name : string) =
    let idx = idx_of_name name !names 0 in
    if idx >= !names_size then
      raise (Name_Not_found ("Symbol: '" ^ name ^ "' is not registered."))
    else
      !names_size -1 - idx

  let get_name_opt (name : string) =
    let idx = idx_of_name name !names 0 in
    if idx >= !names_size then
      None
    else
      Some (!names_size - 1 - idx)

  let register new_name =
    match (get_name_opt new_name) with
    | None ->
      let n = !names_size in (
        names_size := n + 1;
        names := new_name :: !names;
        n)
    | Some _ ->
      (* Now if a name is already registered we return it and don't
          change the internal state of the module. *)
      get_name new_name

  let rec gen_name' i =
    let generated_name = "gN_" ^ (Int.to_string i) in
    match get_name_opt generated_name with
    | None ->
      register generated_name
    | Some _ ->
      gen_name' (i + 1)

  let gen_name _ = gen_name' !names_size

  let compare = Int.compare

  let to_string name = List.nth !names (!names_size -1 -name)

  let name_list _ = List.init !names_size Fun.id

end

module _ : Set.OrderedType = IndexedNames ()
module _ : Map.OrderedType = IndexedNames ()
