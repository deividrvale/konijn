open Term
module Ty = Simple_type
exception RuleInvalid of string

(*-----------------------------------------------------------------------------
  Rewriting rules and TRSs
-----------------------------------------------------------------------------*)

type rule = term * term

type rule_error =
  | VR_in_VL of rule | Var of rule
  | FnHead of rule   | TypeMismatch of rule

let lhs = fst

let rhs = snd

let to_string r =
  Term.to_string (lhs r) ^
  " ==> " ^
  Term.to_string (rhs r)

let equal (r : rule) (r' : rule) : bool =
  match (r, r') with
  | ((lhs, rhs), (lhs', rhs')) ->
    (Term.equal lhs lhs') && (Term.equal rhs rhs')

let is_valid_rule ((lhs, rhs) : rule ) =
  let fv_l = free_var lhs and fv_r = free_var rhs in
  let cond_0 = Ty.equal (Term.type_infer lhs) (Term.type_infer rhs) in
  let cond_1 =
    List.for_all (fun v -> Utils.Lists.member Term.VarSym.equal v fv_l) fv_r in
  let cond_2 = not (is_var lhs) and cond_3 = is_headed_fn lhs in
  (* For performance reasons, we evaluate conditions in reversed order. *)
  if not cond_3 then Either.Left (FnHead (lhs,rhs)) else
    if not cond_2 then Either.Left (Var (lhs, rhs)) else
      if not cond_1 then Either.Left ((VR_in_VL (lhs,rhs))) else
        if not cond_0 then Either.left ((TypeMismatch (lhs,rhs))) else
        Either.right (cond_3 && cond_2 && cond_1 && cond_0)

let rule_error_to_string err =
  match err with
  | VR_in_VL (lhs, rhs) ->
    "Invalid rule " ^ (to_string (lhs, rhs)) ^ ".
    The free variables in the right-hand side (" ^
    (Term.to_string rhs) ^ ") must be contained in the lhs."
  | Var (lhs, rhs) ->
    "Invalid rule " ^ (to_string (lhs, rhs)) ^ ". " ^
    "The left-hand-side " ^ (Term.to_string lhs) ^ "is a variable."
  | FnHead (lhs, rhs) ->
    "Invalid rule " ^ (to_string (lhs, rhs)) ^ ".
    The left-hand-side " ^ (Term.to_string lhs) ^
    " should be headed by a function symbol."
  | TypeMismatch (lhs, rhs) ->
    "Invalid rule " ^ (to_string (lhs, rhs)) ^ ".
    Type mismatch the type " ^ (Ty.ty_to_string (Term.type_infer lhs)) ^
    " of the left-hand side is not equal to the type " ^
    (Ty.ty_to_string (Term.type_infer lhs)) ^ " of the right-hand side."

let rule_mk_opt lhs rhs : rule option =
  match is_valid_rule (lhs, rhs) with
  | Left _ -> None
  | Right status ->
    if status then
      Some (lhs, rhs)
    else
      None

let rule_mk lhs rhs : rule =
  match is_valid_rule (lhs, rhs) with
  | Left (err) -> raise (RuleInvalid (rule_error_to_string err))
  | Right _ -> (lhs, rhs)

(*-----------------------------------------------------------------------------
  Term Rewriting Systems
-----------------------------------------------------------------------------*)

type trs = rule list

let trs_mk rules : trs =
  List.map (fun (l,r) -> rule_mk l r) rules

let get_label rule trs : string =
  "rule_" ^
  Int.to_string (Utils.Lists.index_of equal rule trs)
