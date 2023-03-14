(*-----------------------------------------------------------------------------
  Function Symbols
-----------------------------------------------------------------------------*)
(* Naming State *)
let names : int ref = ref 0

let gensym () =
  names := !names + 1;
  !names

(* Represents a variable name together with its dimention. *)
type abs_name = int * int

let name_equal (x,y) (x', y') =
  Int.equal x x' && Int.equal y y'

let aname_to_string ((name, _) : abs_name )=
  "x" ^ Int.to_string name

type fn = ..
type fn += Max

let fn_to_string = function
  | Max -> "max"
  | _ -> "fn"

type primitive_value =
  | Ind of int * int
  | Var of int * int * int (** name, projection, exponent *)
  | Abs of abs_name * expr
and op =
  | Add of expr * expr
  | Mul of expr * expr
and expr =
  | Num of int
  | Exp of expr * int
  | Val of primitive_value
  | Opr of op
  | App of expr * expr
  | Fn of fn * expr list

(*-----------------------------------------------------------------------------
  Encapsulation for creating expressions
-----------------------------------------------------------------------------*)

let var name proj exp = Val (Var (name, proj, exp))
let add x y = Opr (Add (x,y))
let mul x y = Opr (Mul (x,y))
let pow x i = Exp (x, i)
let abs x e = Val (Abs (x, e))
let app l r = App (l, r)

(*-----------------------------------------------------------------------------
  Operations over expressions
-----------------------------------------------------------------------------*)
module NSet = Set.Make(Int)
type name_set = NSet.t

let rec fvars e =
  let bin_fvars = fun e e' ->
    Utils.Lists.remove_duplicates name_equal ((fvars e) @ (fvars e') ) in
  match e with
  | Num _ -> []
  | Exp (e, _) -> fvars e
  | Val (v) -> begin
    match v with
    | Ind _ -> []
    | Var (name, proj, _) -> [(name, proj)]
    | Abs (x, t) ->
      Utils.Lists.remove name_equal x (fvars t)
    end
  | Opr opr -> begin
    match opr with
    | Add(x,y) -> bin_fvars x y
    | Mul(x,y) -> bin_fvars x y
    end
  | App (e,e') -> bin_fvars e e'
  | Fn (_, es) ->
    es |> List.map fvars |> List.flatten

let is_free name expr =
  Utils.Lists.member name_equal name (fvars expr)

let rename expr n =
  let rec rename_aux expr x x' =
    match expr with
    | Num i -> Num i
    | Exp (e,i) -> Exp (rename_aux e x x', i)
    | Val v -> (
      match v with
        | Ind (i, j) -> Val (Ind (i,j))
        | Var (name, proj, exp) ->
          if name_equal (name, proj) x then
            Val (Var (fst x', snd x', exp))
          else
            Val v
        | Abs (a, t) ->
          if name_equal a x then
            Val (Abs (x', rename_aux t x x'))
          else
            Val (Abs (a,t))
      )
    | Opr opr -> (
        match opr with
        | Add (e,e') -> Opr (Add (rename_aux e x x', rename_aux e' x x'))
        | Mul (e,e') -> Opr (Mul (rename_aux e x x', rename_aux e' x x'))
      )
    | App (e, e') -> App (rename_aux e x x', rename_aux e' x x')
    | Fn (f, args) ->
      let renamed_args = List.map (fun a -> rename_aux a x x') args in
      Fn (f, renamed_args) in
  let new_name = gensym () in
  rename_aux expr n (new_name, snd n)

let rec val_to_string = function
  | Ind (i, _) -> "a" ^ Int.to_string i
  | Var (name, proj, exp) ->
    String.concat ""
    ["x"; Int.to_string name; "_";Int.to_string proj;"^";Int.to_string exp]
  | Abs (x, t) ->
    "λ" ^ aname_to_string x ^ ". " ^ to_string t
and opr_to_string = function
  | Add (x , y) ->
    String.concat "" ["("; to_string x; " + "; to_string y;")"]
  | Mul (x, y) ->
    String.concat "" ["("; to_string x; " * "; to_string y;")"]
and to_string = function
  | Num i -> Int.to_string i
  | Exp (e, i) ->
    String.concat "" [to_string e; "^"; Int.to_string i]
  | Val v -> val_to_string v
  | Opr op -> opr_to_string op
  | App (e, e') ->
    String.concat String.empty [" ("; to_string e; " "; to_string e'; ") "]
  | Fn (fn, es) ->
    String.concat ""
    [fn_to_string fn; Utils.Lists.to_string to_string es]



(*-----------------------------------------------------------------------------
  Reduction and Evaluation
-----------------------------------------------------------------------------*)

type subst = abs_name * expr

let rec is_value = function
  | Num _ -> true
  | Exp (Val (Abs _), _) -> true
  | Val _ -> true
  | Opr (Add (x,y)) ->
    not (add_reduces x y)
  | Opr (Mul (x, y)) ->
    not (mul_reduces x y)
  | App (e, e') ->
    not (app_reduces e e')
  | Fn (_, ls) -> List.for_all is_value ls
  | _ -> false
and app_reduces l r =
  match l, r with
  | Val (Abs _), r when is_value r -> true
  | _,_ -> (not (is_value l)) || (not (is_value r))
and add_reduces x y =
  match x,y with
  | Num 0, _ | _, Num 0 | Num _, Num _ -> true
  | _, _ -> (not (is_value x)) || (not (is_value y))
and mul_reduces x y =
  match x, y with
  | Num 0, _ | _, Num 0 | Num 1, _ | _, Num 1 | Num _, Num _ -> true
  | (Opr Add (_,_)) as l, _ when (is_value l) -> true
  | _, ((Opr Add (_,_)) as r) when (is_value r) -> true
  | _, _ -> (not (is_value x)) || (not (is_value y))
and exp_reduces x i =
  match x,i with
  | _, 0 -> true
  | _, 1 -> true
  | Num _, _ -> true
  | Exp _, _ -> true
  | Opr (Add(_,_)), _ -> true
  | Opr (Mul(_,_)), _ -> true
  | e, _ -> (not (is_value e))

let rec step expr =
  match expr with
  | Exp (e, i) -> step_exp e i

  (* apply lef distribution when the lhs is a value *)
  | Opr Mul ((Opr Add (m,n)) as l, y) when (is_value l) ->
    add (mul m y) (mul n y)

  (* apply right distribution when the rhs is a value *)
  | Opr Mul (x, (Opr Add (m,n) as r)) when (is_value r) ->
    add (mul x m) (mul x n)

  (* step operators *)
  | Opr opr -> step_opr opr

  (* step application *)
  | App (l,r) when not (is_value l) -> App (step l, r)
  | App (l,r) when not (is_value r) -> App (l, step r)

  | (App (Val (Abs (_, _)), _)) as bredex ->
    step_beta bredex
  | _ -> expr
and step_exp e n = (
  match e,n with
  | _, 0 -> Num 1
  | e, 1 -> e
  | Num i, n -> Num (Utils.Math.pow i n)
  | Exp (b, i), n -> Exp (b, i * n)
  | Val (Ind (name, i)), n -> Val (Ind (name, i * n))
  | Val (Var (name, proj, i)), n -> Val (Var (name, proj, i * n))
  | Opr (opr), n ->
    (match opr, n with
    | Add (x,y), 2 ->
      add (add (pow x 2) (mul (mul (Num 2) y) x)) (pow y 2)
    | Add (x, y), n ->
      mul (add x y) (pow (add x y) (n - 1))
    | Mul (x,y), n -> mul (pow x n) (pow y n)
    )
  | _, _ ->
    if is_value e then Exp (e, n) else Exp (step e, n)
  )
and step_opr opr =
  match opr with
    (* Evaluate Addition *)
    | Add (Num 0, e) | Add (e, Num 0) -> e
    | Add (Num i, Num j) -> Num (i + j)
    | Add (x,y) when not (is_value x) ->
      add (step x) y
    | Add (x,y) when not (is_value y) ->
      add x (step y)
    (* Evaluate Multiplication *)
    | Mul (Num 0, _) | Mul (_, Num 0) -> Num 0
    | Mul (Num 1, e) | Mul (e, Num 1) -> e
    | Mul (Num i, Num j) -> Num (i * j)
    | Mul (x,y) when not (is_value x) ->
      mul (step x) y
    | Mul (x,y) when not (is_value y) ->
      mul x (step y)
    (* | _ -> Opr opr *)

and step_beta bredex =
  failwith (to_string bredex)

let rec eval_step (e : expr) =
  if is_value e then
    e
  else
    e |> step |> eval_step

let rec eval_n e n =
  if n = 0 then e
  else
    (* if is_value e then
      failwith "value reached"
    else *)
    eval_n (step e) (n - 1)
