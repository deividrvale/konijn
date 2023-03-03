(*-----------------------------------------------------------------------------
  Type Contexts, Simple Types
-----------------------------------------------------------------------------*)
open Interfaces

(* Base Type Names *)
module BaseTy = Interfaces.Name.IndexedNames ()
type base = BaseTy.t

module IntSet = Set.Make(Int)

type ty = Var of int | Base of base | Arr of ty * ty

(*-----------------------------------------------------------------------------
  Instantiaiton of Context Interfacing
-----------------------------------------------------------------------------*)
module TyCtx (EXP : Base_modules.TOT) =
  struct
    exception Not_found_in_Ctx of string

    type exp = EXP.t
    type t = ty

    let (ctx : (exp, ty) Hashtbl.t) = Hashtbl.create 1000

    let weaken exp ty =
      Hashtbl.add ctx exp ty

    let remove exp =
      Hashtbl.remove ctx exp

    let type_of exp =
      Hashtbl.find_opt ctx exp
end

(*-----------------------------------------------------------------------------
  Setters for Types
-----------------------------------------------------------------------------*)
let base_mk x = Base (BaseTy.register x)
let arr_mk t t' = Arr(t,t')

(*-----------------------------------------------------------------------------
  Basic Operations on ty
-----------------------------------------------------------------------------*)

let rec equal t1 t2 =
  match (t1,t2) with
  | (Var i, Var j) -> Int.equal i j
  | (Base b, Base b') -> BaseTy.equal b b'
  | (Arr (t1, t2), Arr (s1,s2)) ->
    equal t1 s1 && equal t2 s2
  | _ -> false

let rec vars_of = function
  | Base _ -> IntSet.empty
  | Var i -> IntSet.singleton i
  | Arr (a,b) -> IntSet.union (vars_of a) (vars_of b)

let occurs v t =
  IntSet.mem v (vars_of t)

let is_base = function
  Base _ -> true
  | _ -> false

let is_var = function
  Var _ -> true
  | _ -> false

let rec ty_to_string ty =
  match ty with
  | Base b -> BaseTy.to_string b
  | Var i -> Int.to_string i
  | Arr (a,b) ->
    if (is_base a) || (is_var a) then
      (ty_to_string a) ^ " ⟶ " ^ (ty_to_string b)
    else
      "(" ^ (ty_to_string a) ^ ")" ^ " ⟶ " ^ (ty_to_string b)

(*-----------------------------------------------------------------------------
  Substitution over types
-----------------------------------------------------------------------------*)

module IntMap = Map.Make(Int)
type subst = ty IntMap.t

let rec subst_from_list (l : (int * ty) list) : subst =
  match l with
  | [] -> IntMap.empty
  | (i, ty) :: tl ->
    IntMap.add i ty (subst_from_list tl)

let rec apply ty subst =
  match ty with
  | (Base _) as b -> b
  | (Var i) as v -> (
      match IntMap.find_opt i subst  with
      | None -> v
      | Some ty -> ty
    )
  | Arr (t1, t2) -> Arr (apply t1 subst, apply t2 subst)

let apply_list tys subst =
  List.map (fun ty -> apply ty subst) tys

(*-----------------------------------------------------------------------------
  Unification of Types
-----------------------------------------------------------------------------*)
exception TyUnifError of string

type tyEq = ty * ty

let tyEq_to_string (ty1,ty2) =
  (ty_to_string ty1) ^ " =^? " ^ (ty_to_string ty2)

type unifPrb = (tyEq list) * (tyEq list)

let unifPrb_to_string (ps, ss) =
  (Utils.Lists.to_string tyEq_to_string ps) ^
  " || " ^
  (Utils.Lists.to_string tyEq_to_string ss)

let inst_ty_eq ((l,r) : tyEq) (subst : subst) =
  (apply l subst, apply r subst)

let inst_eq_list (el : tyEq list) (subst : subst) : tyEq list =
  List.map (fun eq -> inst_ty_eq eq subst) el

let rec unify ((prb, sol) : unifPrb) : unifPrb =
  match prb with
  (* When the problem list is empty, we are done. *)
  | [] -> ([], sol)
  (* Test for failure cases. *)
  | ((Base _) as s , ((Arr _) as t)) :: _ ->
    raise(TyUnifError
    (String.concat " "
    ["Cannot unify type"; (ty_to_string s); "with"; (ty_to_string t)]))
  | ((Arr _) as s , ((Base _) as t)) :: _ ->
      raise(TyUnifError
      (String.concat " "
      ["Cannot unify type"; (ty_to_string s); "with"; (ty_to_string t)]))
  | ((Base x) as s, ((Base y) as t)) :: tl ->
    if BaseTy.equal x y then
      unify (tl, sol)
    else
      raise (TyUnifError
      (String.concat " "
      ["Cannot unify type"; (ty_to_string s); "with"; (ty_to_string t)]))
  (* Var Elimination a.k.a instantiation rule *)
  | (Var _, _) :: _ -> varElim (prb, sol)
  (* Orient *)
  | (tp, ((Var _) as x)) :: tl ->
    unify ((x, tp) :: tl, sol)
  (* Decompose *)
  | ((Arr(s,t) as l), ((Arr(s', t') as r))) :: tl ->
    if equal l r then
      unify (tl, sol)
    else
      unify ((s,s') :: (t,t') :: tl, sol)
and varElim ((prb, sol) : unifPrb) : unifPrb =
  match prb with
  (* Equation between two variables.
     Here, we apply the rules: TRIVIAL, and Instantiate*)
  | ((Var x, Var y) as eq) :: tl ->
    if Int.equal x y then
      unify (tl, sol)
    else let sigma = IntMap.singleton x (Var y) in
      let (p,s) = (inst_eq_list tl sigma, eq :: (inst_eq_list sol sigma) ) in
      unify (p, s)
  (* Equation between a variable and a type. *)
  | ((Var x, t) as eq) :: tl ->
    if occurs x t then
      raise (TyUnifError ("Occur clash!"))
    else let sigma = IntMap.singleton x t in
      let (p,s) = (inst_eq_list tl sigma, eq :: (inst_eq_list sol sigma)) in
      unify (p,s)
  | _ -> raise (TyUnifError ("Error! Instantiation rule does not apply."))

let verify_mgu prb =
  let verify_eq eq =
    match eq with
    | (Var x, tp) ->
      if occurs x tp then
        false
      else
        true
    | (_, _) -> false
  in
    List.for_all verify_eq prb
