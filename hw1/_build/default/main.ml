(* open Sat 

let f0 = 
  (* Var "Q" *)
  Not (Var "true")
  (* True *)
  (* And (True, False) *)
  (* And (Var "true", Var "false") *)

  (* Not True *)

  (* Var "P" *)
  (* And (
    Imply (Var "P", Var "Q"), 
    And (
      Var "P", Not (Var "Q")
    )
  ) *)

  (* Or (
    And (Var "P", Var "Q"),
    Var "R"
  ) *)

  (* And (
    Or (
      Not (Var "P"), Var "Q"
    ), 
    Or (
      Or (
        Var "R", Not (Var "Q")
      ), Var "S"
    )
  ) *)

  (* Or (
    Not (Var "P"), Var "Q"
  ) *)

  (* Or (
    And (Var "P", Var "Q"), Var "R"
  ) *)

  (* Not (Var "P") *)


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

let test () = 
  List.iter (fun f ->
    print_endline (Sat.string_of_formula f ^ " : " ^ 
      if Sat.solve f then "SAT" else "UNSAT")  
  ) [f0; f1; f2; f3; f4; f5]
  (* ) [f0] *)


let test7 ()
= let _ = Random.init 20240403 in
  let gen_rand_var
  = fun () -> 
    let x = Random.int 6 in
    match x with
    | 0 -> Var("p")
    | 1 -> Var("q")
    | 2 -> Var("r")
    | 3 -> Var("s")
    | 4 -> True
    | 5 -> False
    | _ -> raise (Failure "gen_rand_var")
  in
  let rec gen_rand_formula
  = fun cnt ->
    if cnt = 0 then gen_rand_var ()
    else if cnt = 1 then
      let f = Random.int 2 in
      match f with
      | 0 -> Not(gen_rand_formula (cnt-1))
      | 1 -> gen_rand_var ()
      | _ -> raise (Failure "gen_rand_formula")
    else
      let f = Random.int 5 in
      let r1 = Random.int (cnt - 1) in
      let r2 = cnt - 1 - r1 in
      match f with
      | 0 -> And(gen_rand_formula r1, gen_rand_formula r2)
      | 1 -> Or(gen_rand_formula r1, gen_rand_formula r2)
      | 2 -> Imply(gen_rand_formula r1, gen_rand_formula r2)
      | 3 -> Iff(gen_rand_formula r1, gen_rand_formula r2)
      | 4 -> Not(gen_rand_formula (cnt-1))
      | _ -> raise (Failure "gen_rand_formula")
  in
  let oc = open_out "test30.txt" in
  let tc = List.map (fun _ -> gen_rand_formula 30) (Utils.range 30000) in
    List.iter (fun f ->
      Printf.fprintf oc "%s\n" (Sat.string_of_formula f ^ " : " ^ 
        if Sat.solve f then "SAT" else "UNSAT")
    ) tc  

let _ = test7 () *)

open Sat 
(* open Z3sat *)

let string_of_var: var -> string=fun f -> f ;;
let rec fmla2z3: formula -> Z3sat.formula 
=fun f ->
  match f with
  | True -> Z3sat.True | False -> Z3sat.False | Var v -> Z3sat.Var v 
  | Not f -> Z3sat.Not (fmla2z3 f) 
  | And (f1, f2) -> Z3sat.And (fmla2z3 f1, fmla2z3 f2) 
  | Or (f1, f2) -> Z3sat.Or (fmla2z3 f1, fmla2z3 f2) 
  | Imply (f1, f2) -> Z3sat.Imply (fmla2z3 f1, fmla2z3 f2) 
  | Iff (f1, f2) -> Z3sat.Iff (fmla2z3 f1, fmla2z3 f2)
;;

let test7 ()
= let _ = Random.init 20240403 in
  let gen_rand_var
  = fun () -> 
    let x = Random.int 6 in
    match x with
    | 0 -> Var("p")
    | 1 -> Var("q")
    | 2 -> Var("r")
    | 3 -> Var("s")
    | 4 -> True
    | 5 -> False
    | _ -> raise (Failure "gen_rand_var")
  in
  let rec gen_rand_formula
  = fun cnt ->
    if cnt = 0 then gen_rand_var ()
    else if cnt = 1 then
      let f = Random.int 2 in
      match f with
      | 0 -> Not(gen_rand_formula (cnt-1))
      | 1 -> gen_rand_var ()
      | _ -> raise (Failure "gen_rand_formula")
    else
      let f = Random.int 5 in
      let r1 = Random.int (cnt - 1) in
      let r2 = cnt - 1 - r1 in
      match f with
      | 0 -> And(gen_rand_formula r1, gen_rand_formula r2)
      | 1 -> Or(gen_rand_formula r1, gen_rand_formula r2)
      | 2 -> Imply(gen_rand_formula r1, gen_rand_formula r2)
      | 3 -> Iff(gen_rand_formula r1, gen_rand_formula r2)
      | 4 -> Not(gen_rand_formula (cnt-1))
      | _ -> raise (Failure "gen_rand_formula")
  in
  let oc = open_out "test30.txt" in
  let tc = List.map (fun _ -> gen_rand_formula 30) (Utils.range 3000) in
  List.iter (fun f ->
    let z3_res = Z3sat.test_sat (fmla2z3 f) in
    let my_res = Sat.solve f in
    Printf.fprintf oc "%s\n" (
      if z3_res = my_res 
      then ("Correct ") 
      else ("Wrong : "
        ^ Sat.string_of_formula f ^ " : " 
        ^ "YOU: " ^ string_of_bool my_res ^ " / Z3: " ^ string_of_bool z3_res ) 
      )
  ) tc  ;;
test7 ();;