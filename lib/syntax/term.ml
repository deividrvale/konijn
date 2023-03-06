module ST = Simple_type

(*-----------------------------------------------------------------------------
  Function Symbols
-----------------------------------------------------------------------------*)

module FnSym = Name.IndexedNames ()
type fn = FnSym.t

module FnCtx = (ST.TyCtx(FnSym) : Context.TY_CTX
  with type exp = fn and type t = ST.ty)

(*-----------------------------------------------------------------------------
  Variable Symbols
-----------------------------------------------------------------------------*)

module VarSym = Name.IndexedNames ()
type var = VarSym.t

module VarCtx = (ST.TyCtx(VarSym) : Context.TY_CTX
  with type exp = var and type t = ST.ty)

(*-----------------------------------------------------------------------------
  Terms
-----------------------------------------------------------------------------*)
type term =
  | Fun of fn
  | Var of var
  | Lam of var * term
  | App of term * term

let var_mk x = Var x
let fn_mk f = Fun f
let app_mk l r = App(l,r)
let lam_mk x t = Lam(x,t)

let free_var t =
  let rec fvar_acc = (fun t acc ->
    match t with
    | Fun _ -> []
    | Var v -> Utils.Lists.cons_uniq VarSym.equal v acc
    | App (t1,t2) ->
      (fvar_acc t1 acc) @ (fvar_acc t2 acc)
    | Lam (v, t') -> Utils.Lists.remove VarSym.equal v (fvar_acc t' acc)
    )
  in Utils.Lists.remove_duplicates VarSym.equal (fvar_acc t [])

let is_var = function
  | Var _ -> true
  | _ -> false

let is_headed_fn = function
  | Fun _ -> true
  | App (Fun _, _) -> true
  | _ -> false


let is_free x t =
  let fvars = free_var t in
  Utils.Lists.member VarSym.equal x fvars

(* to_string *)
let rec tm_to_string' (b : bool) (t : term) =
  match t with
  | Fun f -> FnSym.to_string f
  | Var x -> VarSym.to_string x
  | e -> (
    if b then
      print_app e
    else
      "(" ^ print_lambda e ^ ")"
  )
and print_app = function
  | e -> print_other_app e
and print_other_app f =
  match f with
  | App (f, x) -> print_app f ^ " · " ^ (tm_to_string' false x)
  | f -> tm_to_string' false f
and print_lambda = function
  | Lam (v, t) ->
    "λ" ^ VarSym.to_string v ^ "." ^ print_lambda t
  | e -> print_app e

let to_string = tm_to_string' true

(*-----------------------------------------------------------------------------
  Renaming and Barendregt Conditions
-----------------------------------------------------------------------------*)

let rec rename t v v' =
  match t with
  | Fun f -> Fun f
  | Var x ->
    if VarSym.equal x v then Var v' else Var x
  | Lam (x,t') ->
    if VarSym.equal x v then Lam (x,t')
      else Lam (x, rename t' v v')
  | App(m,n) -> App (rename m v v', rename n v v')

let is_barendregt t =
  let rec biding_var = function
    | Lam (x, s') -> [x] @ biding_var s'
    | Fun _ -> []
    | Var _ -> []
    | App (m,n) -> (biding_var m) @ (biding_var n) in
  let bv  = biding_var t in
  let bv' = Utils.Lists.remove_duplicates VarSym.equal bv in
  Int.equal (List.length bv) (List.length bv')

let rename_fvar_to_fresh s v =
  let fresh_var = VarSym.gen_name () in
  rename s v fresh_var

let rec to_barendregt s =
  if is_barendregt s then s else
    begin
      match s with
      | Fun f -> Fun f
      | Var x -> Var x
      | Lam (x,t') -> let fresh_var = VarSym.gen_name () in
        Lam (fresh_var, to_barendregt (rename t' x fresh_var))
      | App (m,n) ->
        App (to_barendregt m, to_barendregt n)
    end

(*-----------------------------------------------------------------------------
  Substitution over terms
-----------------------------------------------------------------------------*)
module TSubst = Map.Make(VarSym)
type subst = term TSubst.t

let is_closed t =
  not (List.length (free_var t) > 0)

let rec subst_from_list (l : (var * term) list) : subst =
  match l with
  | [] -> TSubst.empty
  | (v, t) :: tl ->
    TSubst.add v t (subst_from_list tl)

let rec apply tm subst =
  if is_closed tm then tm
  else begin
    match tm with
    | Fun f -> Fun f
    | (Var x) as v -> (
        match TSubst.find_opt x subst with
        | None -> v
        | Some t -> t
      )
    | App (m,n) -> App (apply m subst, apply n subst)
    | Lam(x,t) ->
      let occurs = TSubst.filter (fun _ t -> is_free x t) subst in
      match TSubst.min_binding_opt occurs with
      | None ->
        Lam (x, apply t subst)
      | Some _ ->
        let fresh_var = VarSym.gen_name () in
        let t' = rename t x fresh_var in
        Lam (fresh_var, apply t' subst)
  end

(*-----------------------------------------------------------------------------
  Typing
-----------------------------------------------------------------------------*)

(* Rename all bound variables to different names. *)
let rec gen_ty_eq = function
  | Fun f -> (FnCtx.type_of  f, [])
  | Var x -> (VarCtx.type_of x, [])
  | App (m,n) ->
      let (tpM, eqM) = gen_ty_eq m in
      let (tpN, eqN) = gen_ty_eq n in
      let fresh_ty = ST.fresh_ty () in
      let eqApp = eqM @ eqN @ [(tpM, (ST.arr_mk tpN fresh_ty))] in
        (fresh_ty, eqApp)
  | Lam (x, m) ->
      let fresh_ty = ST.fresh_ty () in
      VarCtx.weaken x fresh_ty;
      let (tpM, eqM) = gen_ty_eq m in
        (ST.arr_mk fresh_ty tpM, eqM)

let type_infer =
  ST.ty_infer gen_ty_eq

(*-----------------------------------------------------------------------------
    de Bruijn Terms
-----------------------------------------------------------------------------*)
type ('f, 'v) bruijn =
    | NFun of 'f
    | NVar of 'v
    | NLam of ('f, 'v) bruijn
    | NApp of ('f, 'v) bruijn * ('f, 'v) bruijn

type nameless = (fn, int) bruijn

let rec terms_to_bruijn_ctx ctx (tm : term) : nameless =
  match tm with
  | Fun f -> NFun f
  | Var v ->
    NVar (Utils.Lists.index_of VarSym.equal v ctx)
  | Lam (v, t) ->
    NLam (terms_to_bruijn_ctx (v :: ctx) t)
  | App (s, t) ->
    NApp (
      (terms_to_bruijn_ctx ctx s),
      (terms_to_bruijn_ctx ctx t)
    )

let terms_to_bruijn t =
  terms_to_bruijn_ctx (free_var t) t

let rec nameless_to_string' (is_root : bool) (t : nameless) =
  match t with
  | NFun f -> FnSym.to_string f
  | NVar i -> " V " ^ (Int.to_string i)
  | e -> (
    if is_root then
      show_app e
    else
      "(" ^ show_lam e ^ ")"
  )
and show_app = function
  | NApp (f, x) -> show_app f ^ " · " ^ (nameless_to_string' false x)
  | e -> nameless_to_string' false e
and show_lam = function
  | NLam t -> "λ " ^ show_lam t
  | e -> show_app e

let nameless_to_string = nameless_to_string' false

let rec nameless_equal (s : nameless) (t : nameless) : bool =
  match (s,t) with
  | (NVar x, NVar y) -> x == y
  | (NFun x, NFun y) -> FnSym.equal x y
  | (NApp (s,s'), NApp (t,t')) ->
    (nameless_equal s t) && (nameless_equal s' t')
  | (NLam s, NLam t) -> nameless_equal s t
  | _ -> false

let equal (s : term) (t : term) : bool =
  let (nml_s, nml_t) =
    (terms_to_bruijn s, terms_to_bruijn t)
  in nameless_equal nml_s nml_t
