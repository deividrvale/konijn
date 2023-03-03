(* Polymorphic utilities over lists. *)
(* index_of needs an equality operator on the elements of the list *)
let rec index_of' (eq : ('a -> 'a -> bool)) (x : 'a) (xs : 'a list) (idx : int)
                  : int =
  match xs with
  | [] -> raise Not_found
  | hd :: tl ->
    if (eq x hd) then
      idx
    else
      index_of' eq x tl (idx + 1)

let index_of eq x xs =
  index_of' eq x xs (-1)

let remove (eq : 'a -> 'a -> bool) (x : 'a) (xs : 'a list) : 'a list =
  List.filter (fun e -> not (eq x e)) xs

let print_list (f : 'a -> string) (xs : 'a list) : unit =
  print_endline (
    "[" ^ (String.concat ";" (List.map f xs)) ^ "]"
  )

let to_string (f : 'a -> string) (xs : 'a list) : string =
  "[" ^ (String.concat ";" (List.map f xs)) ^ "]"

let member (eq : 'a -> 'a -> bool) (x : 'a) (xs : 'a list) : bool =
  let xs_eq =
    List.filter (fun y -> eq x y) xs
  in match xs_eq with
  | [] -> false
  | _ :: _ -> true

let cons_uniq (eq : 'a -> 'a -> bool) (x : 'a) (xs : 'a list) =
  if (member eq x xs) then xs else x :: xs

let remove_duplicates (eq : 'a -> 'a -> bool) (xs : 'a list) : 'a list =
  List.rev (List.fold_left (fun ys y -> cons_uniq eq y ys) [] xs)
