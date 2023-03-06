open Syntax.Simple_type
open Syntax.Term
(* Declare some sorts *)
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

let () = FnCtx.weaken (FSym.get_name "f") (arr_mk nat nat)

let abst = lam_mk x (lam_mk y (app_mk (var_mk x) (
  lam_mk x (Var (VSym.register "z"))
)))

let sub = subst_from_list [(VSym.register "z", f)]

let abst_b = to_barendregt_conv abst
let () =
  is_barendregt abst |> Bool.to_string |> print_endline;
  print_endline (tm_to_string abst);
  tm_to_string abst_b |> print_endline;
  tm_to_string (apply abst sub) |> print_endline;

  (*
let ty_unif_pair = gen_ty_eq abst

let infered_ty = ty_infer gen_ty_eq abst

let () =
  print_endline (ty_to_string (ty_unif_pair |> fst));
  print_endline (unifPrb_to_string ([],ty_unif_pair |> snd));
  print_endline (ty_to_string infered_ty) *)
