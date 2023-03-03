(** Utility functions for lists.
*)

val index_of : ('a -> 'a -> bool) -> 'a -> 'a list -> int
(**
    [index_of f x xs] is the index of x in xs
    utilizing [f] as equality operator.
    @raise Not_found if [x] is not a member of [xs].
*)

val member : ('a -> 'a -> bool) -> 'a -> 'a list -> bool
(**
    [member f x xs] is whether [x] occurs in [xs],
    equality tests is done by [f].
*)

val remove : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
(**
    [remove f x xs] removes [x] from [xs]
    utilizing [f] as equality operator.
*)

val print_list : ('a -> string) -> 'a list -> unit
(**
    [print_list f xs] prints the the list to {b stdout}
    utilizing [f].
*)

val to_string : ('a -> string) -> 'a list -> string
(**
    [to_string f xs] return a string representation of [xs] utilizing [f].
*)

val cons_uniq : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
(**
    [cons_uniq f x xs] is like [List.cons]
    but [x] is added to the list iff it is not a member of [xs],
    [f] is used as equality operator.
*)

val remove_duplicates : ('a -> 'a -> bool) -> 'a list -> 'a list
(**
    [remove_duplicates f xs] removes duplicated elements from [xs] utilizing [f] as equality operator.
*)
