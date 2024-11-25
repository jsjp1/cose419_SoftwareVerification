(* open Smt 

exception Not_implemented

type var = string  

type formula = 
  | True 
  | False 
  | Var of var 
  | Not of formula 
  | And of formula * formula
  | Or of formula * formula 
  | Imply of formula * formula
  | Iff of formula * formula

let rec string_of_formula f = 
  match f with 
  | True -> "true"
  | False -> "false"
  | Var x -> x 
  | Not f -> "not " ^ string_of_formula f 
  | And (f1, f2) -> "(" ^ string_of_formula f1 ^ " and " ^ string_of_formula f2 ^ ")"
  | Or (f1, f2) -> "(" ^ string_of_formula f1 ^ " or " ^ string_of_formula f2 ^ ")"
  | Imply (f1, f2) -> "(" ^ string_of_formula f1 ^ " -> " ^ string_of_formula f2 ^ ")"
  | Iff (f1, f2) -> "(" ^ string_of_formula f1 ^ " <-> " ^ string_of_formula f2 ^ ")"

let rec trans : formula -> Fmla.t 
=fun f ->
  match f with
  | True -> Fmla.true_()
  | False -> Fmla.false_()
  | Var x -> Expr.create_var (Expr.sort_of_bool()) ~name:x
  | Not f -> Fmla.create_not (trans f)
  | And (f1, f2) -> Fmla.create_and [trans f1; trans f2]
  | Or (f1, f2) -> Fmla.create_or [trans f1; trans f2]
  | Imply (f1, f2) -> Fmla.create_imply (trans f1) (trans f2)
  | Iff (f1, f2) -> Fmla.create_iff (trans f1) (trans f2)

let check_sat : formula -> bool * Model.t option 
=fun f -> 
  let v, model_opt = Solver.check_satisfiability [trans f] in 
    if Solver.is_sat v then           
      match model_opt with 
      | Some model -> (true, Some model)
      | None -> raise (Failure "check_sat")
    else (false, None)

let check_valid : formula -> bool * Model.t option 
=fun f -> 
  let v, model_opt = Solver.check_validity [trans f] in 
    if Solver.is_valid v then (true, None)
    else 
      match model_opt with 
      | Some model -> (false, Some model) 
      | None -> raise (Failure "check_valid")
  
let f1 = 
  Imply (
    And (
      Var "P", 
      Var "Q"
    ), 
    Imply (
      Var "P", 
      Var "Q"
    )
  )

let f2 = 
  Or (
    Imply (Var "P", Var "Q"), 
    And (
      Var "P", 
      Not (Var "Q")
    )
  )

let f3 = 
  Imply (
    Imply (
      Var "P", 
      Imply (
        Var "Q", 
        Var "R"
      )
    ), 
    Imply (
      Var "P",
      Var "Q"
    )
  )

let f4 = 
  Imply (
    Imply (
      Var "P", 
      Or (
        Var "Q", 
        Var "R"
      )  
    ), 
    Imply (
      Var "P", 
      Var "Q"
    )
  )

let f5 = 
  Imply (
    Not (And (Var "P", Var "Q")), 
    Imply ( 
      Var "R", 
      Imply (
        Not (Var "R"),
        Var "Q"
      )
    )
  )

let test f = 
  match check_valid f with 
  | true, None -> print_endline (string_of_formula f ^ " is valid")
  | false, Some m -> print_endline (string_of_formula f ^ " is invalid. Model = " ^ Model.to_string m)
  | _ -> raise (Failure "unknown") 

let run () = 
  List.iter (fun f -> 
    test f; 
    print_endline ""
  ) [f1; f2; f3; f4; f5] *)

  open Smt

exception Not_implemented

type var = string  

type formula = 
  | True 
  | False 
  | Var of var 
  | Not of formula 
  | And of formula * formula
  | Or of formula * formula 
  | Imply of formula * formula
  | Iff of formula * formula

let rec string_of_formula f = 
  match f with 
  | True -> "true"
  | False -> "false"
  | Var x -> x 
  | Not f -> "not " ^ string_of_formula f 
  | And (f1, f2) -> "(" ^ string_of_formula f1 ^ " and " ^ string_of_formula f2 ^ ")"
  | Or (f1, f2) -> "(" ^ string_of_formula f1 ^ " or " ^ string_of_formula f2 ^ ")"
  | Imply (f1, f2) -> "(" ^ string_of_formula f1 ^ " -> " ^ string_of_formula f2 ^ ")"
  | Iff (f1, f2) -> "(" ^ string_of_formula f1 ^ " <-> " ^ string_of_formula f2 ^ ")"

let rec trans : formula -> Fmla.t 
=fun f -> match f with
  | True -> Fmla.true_ ()
  | False -> Fmla.false_ ()
  | Var x -> Expr.create_var (Expr.sort_of_bool()) ~name: x
  | Not f -> Fmla.create_not (trans f)
  | And (f1, f2) -> Fmla.create_and [trans f1; trans f2]
  | Or (f1, f2) -> Fmla.create_or [trans f1; trans f2]
  | Imply (f1, f2) -> Fmla.create_imply (trans f1) (trans f2)
  | Iff (f1, f2) -> Fmla.create_iff (trans f1) (trans f2)

let check_sat : formula -> bool * Model.t option 
=fun f -> 
  let v, _model_opt = Solver.check_satisfiability [trans f] in 
    if Solver.is_sat v then 
      (true, None)
      (* match model_opt with 
      | Some model -> (true, Some model)
      | None -> raise (Failure "check_sat") *)
    else (false, None)

let check_valid : formula -> bool * Model.t option 
=fun f -> 
  let v, model_opt = Solver.check_validity [trans f] in 
    if Solver.is_valid v then (true, None)
    else 
      match model_opt with 
      | Some model -> (false, Some model) 
      | None -> raise (Failure "check_valid")
  
(* let f1 = 
  Imply (
    And (
      Var "P", 
      Var "Q"
    ), 
    Imply (
      Var "P", 
      Var "Q"
    )
  )

let f2 = 
  Or (
    Imply (Var "P", Var "Q"), 
    And (
      Var "P", 
      Not (Var "Q")
    )
  )

let f3 = 
  Imply (
    Imply (
      Var "P", 
      Imply (
        Var "Q", 
        Var "R"
      )
    ), 
    Imply (
      Var "P",
      Var "Q"
    )
  )

let f4 = 
  Imply (
    Imply (
      Var "P", 
      Or (
        Var "Q", 
        Var "R"
      )  
    ), 
    Imply (
      Var "P", 
      Var "Q"
    )
  )

let f5 = 
  Imply (
    Not (And (Var "P", Var "Q")), 
    Imply ( 
      Var "R", 
      Imply (
        Not (Var "R"),
        Var "Q"
      )
    )
  ) *)
  let test f = 
    match check_valid f with 
    | true, None -> print_endline (string_of_formula f ^ " is valid")
    | false, Some m -> print_endline (string_of_formula f ^ " is invalid. Model = " ^ Model.to_string m)
    | _ -> raise (Failure "unknown") 
    
let test_sat f = 
  let v, _model_opt = Solver.check_satisfiability [trans f] in 
  match Solver.string_of_satisfiability v with
  | "SAT" -> true
  | "UNSAT" -> false
  | _ -> raise (Failure "unknown in test_sat")
  (* print_endline(string_of_formula f ^ " is "^Solver.string_of_satisfiability v) *)
  (* match check_sat f with 
  | true, None -> print_endline (string_of_formula f ^ " is SAT")
  | false, Some m -> print_endline (string_of_formula f ^ " is UNSAT. Model = " ^ Model.to_string m)
  | _ -> raise (Failure "unknown")  *)

let f6 = True 
let f7 = Not ( Var "P")
let f8 = Not ( False )
let f9 = Not ( True )

let f1 = 
  Or (
    And (Var "Q1", Var "Q2"), 
    And (Var "R1", Var "R2")
  )

let f2 = False 

let f3 = Not True 

let f4 = 
  And (
    Imply (Var "P", Var "Q"), 
    And (Var "P", Not (Var "Q"))
  )

let f5 = Or (And (Var "P", Var "Q"), Var "R")
let run () = 
  List.iter (fun _ -> 
    (* test_sat f;  *)
    print_endline ""
  ) 
  (* [f6;f7;f8;f9] *)
  [f1; f2; f3; f4; f5]
