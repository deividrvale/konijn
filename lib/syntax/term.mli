(*-----------------------------------------------------------------------------
  Function Symbols
-----------------------------------------------------------------------------*)

module FnSym : Name.NAME

type fn = FnSym.t

module FnCtx : Context.TY_CTX with type exp = fn and type t = Simple_type.ty

(*-----------------------------------------------------------------------------
  Variable Symbols
-----------------------------------------------------------------------------*)
module VarSym : Name.NAME
type var = VarSym.t

module VarCtx : Context.TY_CTX with type exp = var and type t = Simple_type.ty

(*-----------------------------------------------------------------------------
  Terms
-----------------------------------------------------------------------------*)
type term =
  | Fun of fn
  | Var of var
  | Lam of var * term
  | App of term * term

(*  *)
val var_mk : var -> term
val fn_mk : fn -> term
val app_mk : term -> term -> term
val lam_mk : var -> term -> term

val free_var : term -> var list

val is_free : var -> term -> bool

val is_var : term -> bool

val is_closed : term -> bool

val is_headed_fn : term -> bool

val to_string : term -> string

val equal : term -> term -> bool

(*-----------------------------------------------------------------------------
  Renaming and Barendregt Conditions
-----------------------------------------------------------------------------*)

val rename : term -> var -> var -> term
(** [rename t x y] is the term in which
    every free instance of [x] is replaced by [y] *)

val rename_fvar_to_fresh : term -> var -> term

val is_barendregt : term -> bool

val to_barendregt : term -> term

(*-----------------------------------------------------------------------------
  Substitution over terms
-----------------------------------------------------------------------------*)
type subst

val subst_from_list : (var * term) list -> subst

val apply : term -> subst -> term

(*-----------------------------------------------------------------------------
  Typing
-----------------------------------------------------------------------------*)
val type_infer : term -> Simple_type.ty
