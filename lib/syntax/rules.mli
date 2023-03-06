exception RuleInvalid of string

type rule

type trs

val rule_mk : Term.term -> Term.term -> rule

val trs_mk : rule list -> trs

val lhs : rule -> Term.term

val rhs : rule -> Term.term

val equal : rule -> rule -> bool

val to_string : rule -> string

val get_label : rule -> trs -> string
