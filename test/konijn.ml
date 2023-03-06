(* open Syntax.Simple_type
open Syntax.Term

let nat = base_mk "nat"
let list = base_mk "list"

let zero = FSym.register "zero"
let x = VSym.register "x"
let y = VSym.register "y"

(* let () = VarCtx.weaken y nat *)

let f_s = FSym.register "f"

let _ = FnCtx.weaken f_s (ST.arr_mk nat nat)

let f =
  app_mk
  (fn_mk f_s)
  (app_mk
    (lam_mk x (Var x))
    (Var x)
  )

let () = FnCtx.weaken (FSym.of_string "f") (arr_mk nat nat)

let abst = lam_mk x (lam_mk y (app_mk (var_mk x) (
  lam_mk x (Var (VSym.register "z"))
)))

let sub = subst_from_list [(VSym.register "z", f)]

let abst_b = to_barendregt_conv abst
let () =
  is_barendregt abst |> Bool.to_string |> print_endline;
  print_endline (tm_to_string abst);
  tm_to_string abst_b |> print_endline;
  tm_to_string (apply abst sub) |> print_endline; *)

open Syntax
open Syntax.Term
let f = FnSym.register "a"
let x = VarSym.register "x"

let lhs = fn_mk f
let rhs = var_mk x

let rule = Rules.rule_mk lhs rhs
