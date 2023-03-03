open Interfaces.Name
open Syntax.Simple_type

module V = IndexedNames ()

let _ = V.gen_name ()

let _ = V.register "teste"

let _ = V.register "teste"

let _ = V.gen_name ()

let nat = base_mk "nat"
let list = base_mk "list"

let ty_var = Var 1

let ty' = arr_mk (Var 1) (Var 2)

let ty = arr_mk nat (Var 1)

let s = (subst_from_list [(1, ty'); (2, ty')])

let () =
  Utils.Lists.print_list BaseTy.to_string (BaseTy.name_list ());
  print_endline (ty_to_string ty');
  print_endline (ty_to_string (apply ty' s))

let uprob = ([(ty, ty')], [])

let sol = unify uprob

let () =
  print_endline (unifPrb_to_string sol)

open Syntax.Term

let zero = FSym.register "zero"

let () = FnCtx.weaken zero ty

let ty_of_zero = FnCtx.type_of zero

let () =
  match ty_of_zero with
  | None -> ()
  | Some t -> print_endline (ty_to_string t)
