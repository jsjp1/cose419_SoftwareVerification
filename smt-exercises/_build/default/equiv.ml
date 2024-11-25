(* open Utils *)
open Smt 
      
type var = string 
type exp = 
  | Var of var 
  | Not of exp 
  | And of exp * exp 
  | If of exp * exp * exp 

let e1 = If (And (Not (Var "a"), 
                  Not (Var "b")), 
             Var "h", 
             If (Not (Var "a"), 
                 Var "g", 
                 Var "f"))
let e2 = If (Var "a", 
             Var "f", 
             If (Var "b", Var "g", Var "h"))

let e3 = If (And (Var "a", Var "b"), Var "a", Var "b")
let e4 = If (And (Var "a", Var "b"), Var "b", Var "a")

let check_sat f = 
  let _ = prerr_endline ("\n" ^ Fmla.to_string f) in 
  let (v, model_opt) = Solver.check_satisfiability [f] in 
  let _ = prerr_endline (Solver.string_of_satisfiability v) in 
    match model_opt with 
    | Some model -> prerr_endline (Model.to_string model); true 
    | None -> false 

module Env = struct 
  type t = (var, Expr.t) BatMap.t

  let empty = BatMap.empty
  let lookup = BatMap.find
  let add x env =
    BatMap.add x 
    (Expr.create_var (Expr.sort_of_bool()) ~name:x) env
end

let rec trans : exp -> Env.t -> Fmla.t
=fun e env ->
  match e with
  | Var x -> Env.lookup x env
  | Not e1 -> Fmla.create_not (trans e1 env)
  | And (e1, e2) -> Fmla.create_and [trans e1 env; trans e2 env]
  | If (e1, e2, e3) -> Fmla.create_or [
    Fmla.create_and [trans e1 env; trans e2 env];
    Fmla.create_and [Fmla.create_not (trans e1 env); (trans e3 env)]
    ]

let rec collect_vars e =
  match e with
  | Var _ -> BatSet.singleton
  | Not e1 -> (collect_vars e1)
  | And (e1, e2) -> BatSet.union (collect_vars e1) (collect_vars e2)
  | If (e1, e2, e3) ->
    BatSet.union (
      (BatSet.union (collect_vars e1) (collect_vars e2))
      collect_vars e3
    )

let create_env e1 e2 = 
  let vars = collect_vars (And(e1, e2)) in
    BatSet.fold Env.add vars Env.empty


let verify_equiv : exp -> exp -> bool 
=fun e1 e2 ->
  let env = create_env e1 e2 in
  let f1 = trans e1 env in 
  let f2 = trans e2 env in
    let f = Fmla.create_not (Fmla.create_iff f1 f2) in
      check_sat f

let run () = 
  let _ = verify_equiv e1 e2 in 
  let _ = verify_equiv e3 e4 in 
    ()