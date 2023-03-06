open Term
module Ty = Simple_type
exception RuleInvalid of string

(*-----------------------------------------------------------------------------
  Rewriting rules and TRSs
-----------------------------------------------------------------------------*)

type rule = term * term

type rule_error = VR_in_VL of rule | Var of rule | FnHead of rule

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

let is_valid_rule ((lhs, rhs) : rule ) : bool =
  let fv_l = free_var lhs and fv_r = free_var rhs in
  let cond_1 =
    List.for_all (fun v -> Utils.Lists.member Term.VarSym.equal v fv_l) fv_r in
  let cond_2 = not (is_var lhs) and cond_3 = is_headed_fn lhs in
  (* For performance reasons, we evaluate conditions in reversed order. *)
  cond_3 && cond_2 && cond_1

let rule_mk_opt lhs rhs : rule option =
  if (is_valid_rule (lhs, rhs)) then
    Some (lhs, rhs)
  else
    None

let rule_mk lhs rhs : rule =
  match rule_mk_opt lhs rhs with
  | None -> raise
    (RuleInvalid ("The pair " ^ to_string (lhs, rhs) ^ " is not valid."))
  | Some r -> r

(*-----------------------------------------------------------------------------
  Term Rewriting Systems
-----------------------------------------------------------------------------*)

type trs = rule list

let trs_mk rules = rules

let get_label rule trs : string =
  "rule_" ^
  Int.to_string (Utils.Lists.index_of equal rule trs)
