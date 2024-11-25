type var = string
type formula =
    False
  | True
  | Var of var
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imply of formula * formula
  | Iff of formula * formula
val string_of_formula : formula -> var
type literal = bool * var
type clause = literal list
type cnf = clause list
val string_of_literal : bool * var -> var
val string_of_clause : (bool * var) list -> var
val string_of_cnf : (bool * var) list list -> var
exception Not_implemented
val convert : formula -> cnf
val subst : cnf -> bool -> var -> cnf
val bcp : cnf -> cnf
val ple : cnf -> cnf
val choose : cnf -> var
val dpll : cnf -> bool
val solve : formula -> bool
