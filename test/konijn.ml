(* open Syntax.Simple_type
open Syntax.Term



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

(* open Syntax
open Syntax.Term
open Simple_type
let f = FnSym.register "f"
let x = VarSym.register "x"
let y = VarSym.register "y"

let nat = Simple_type.base_mk "nat"

let () =
  FnCtx.weaken f (arr_mk nat nat);
  VarCtx.weaken x (nat);
  VarCtx.weaken y (nat)

let lhs = app_mk (fn_mk f) (var_mk x)

let rhs = app_mk (fn_mk f) (var_mk y)

let rule = Rules.rule_mk lhs rhs

let () =
  Rules.to_string rule |> print_endline *)

open Tuple.Expr

(* let coef = normalize_coef [Num 1; Num 3; Num 4] @ [Ind (3, IndName.fresh ())] *)

(* let () = *)
  (* coef_to_string coef |> print_endline; *)

(* let a1 = Ind (gensym (), 1) *)

(* let poly = Abs ((gensym (), 1), (Add (Val a1, Val (Num 2)))) *)
let x = gensym ()
let y = gensym ()
(* let test = (var 1 1 1) *)

let test = pow (add (var 2 1 1) (var 1 1 1)) 3

let () =
  print_string "Is value: ";
  is_value test |> Bool.to_string |> print_endline;
  print_string "Poly: ";
  test |> to_string |> print_endline;
  (* print_string "Axiom reduced: "; *)
  (* to_string (algebraic_axioms test) |> print_endline; *)
  print_endline "Poly reduced: ";
  to_string (eval_step test) |> print_endline;
  is_value  (eval_step test) |> Bool.to_string |> print_endline
  (* to_string (eval_n test 3) |> print_endline; *)
  (* is_value ((eval_n test 3)) |> Bool.to_string |> print_endline; *)
  (* to_string (rename test (x,1)) |> print_endline; *)
  (* to_string (rename test (x,1)) |> print_endline; *)
  (* to_string (rename (eval_step test) (x,1)) |> print_endline; *)
