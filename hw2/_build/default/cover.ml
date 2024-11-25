open Smt 
open Utils

type sets = int * int * (int list list)

let sets1 : sets = (6, 7, 
[
  [1;0;0;1;0;0;1]; 
  [1;0;0;1;0;0;0];
  [0;0;0;1;1;0;1]; 
  [0;0;1;0;1;1;0]; 
  [0;1;1;0;0;1;1];
  [0;1;0;0;0;0;1];
])

let sets2 : sets = (4, 4, 
[
  [0; 1; 1; 0];
  [0; 1; 1; 1];
  [1; 1; 0; 0]; 
  [1; 1; 1; 0];
])

let sets3 : sets = (3, 3, 
[
  [0; 1; 1];
  [1; 1; 1];
  [1; 0; 0]
])

type formula = 
  | X of int 
  | T of int * int 
  | Bool of bool 
  | And of formula list 
  | Or of formula list 
  | Not of formula 
  | Imply of formula * formula 
  | Iff of formula * formula 
  | Neq of int * int 

let bigand f l = And (List.map f l)
let bigor f l = Or (List.map f l)

let get_x t i j = List.nth (List.nth t (i)) (j)

let encode : sets -> formula 
(* 
  n -> # of rows 
  m -> # of columns
  t -> 행렬
*)
=fun (n, m, t) -> 
  let c1 = 
    bigand ( fun i ->
      bigor ( fun j ->
        And [X j; T (j, i)]
      ) (range n)
    ) (range m) in
  let c2 = 
    bigand ( fun i ->
      bigand ( fun j ->
        bigand ( fun k ->
          Imply (
            Neq (j, k),
            Imply (
              And [X j; T (j, i)],
              Not (
                And [X k; T (k, i)]
              )
            )
          )
        ) (range n)
      ) (range n)
    ) (range m) in
  let c3 = 
    bigand ( fun i ->
      bigand ( fun j ->
        if get_x t i j = 1 then T (i, j)
        else Not (T (i, j))
      ) (range m)
    ) (range n) in
    And [c1; c2; c3]

let rec trans : formula -> Fmla.t
=fun f ->
  match f with
  | X n -> Expr.create_var (Expr.sort_of_bool()) ~name: ("X" ^ string_of_int n)
  | T (n1, n2) -> Expr.create_var (Expr.sort_of_bool()) ~name: ("T" ^ string_of_int n1 ^ "_" ^ string_of_int n2)
  | Bool b ->
    (
      match b with
      | true -> Expr.true_ ()
      | false -> Expr.false_ ()
    )
  | And fs -> Fmla.create_and (List.map trans fs)
  | Or fs -> Fmla.create_or (List.map trans fs)
  | Not f -> Fmla.create_not (trans f)
  | Imply (f1, f2) -> Fmla.create_imply (trans f1) (trans f2)
  | Iff (f1, f2) -> Fmla.create_iff (trans f1) (trans f2)
  | Neq (n1, n2) -> Expr.create_neq (Expr.of_int n1) (Expr.of_int n2)
  
  
let model2solution : Model.t -> int -> int list
=fun model size ->
  List.map ( fun i ->
    let s = Expr.create_var (Expr.sort_of_bool()) ~name: ("X" ^ string_of_int i) in
    match Model.eval s ~model:model with
    | Some expr ->
      if Expr.to_string expr = "true" then i+1
      else -1
    | _ -> raise (Failure "QQQ")
  ) (range size)
  
let rec extract_size : formula -> BatSet.Int.t -> BatSet.Int.t
=fun f batset ->
  match f with
  | X n -> BatSet.Int.add n batset
  | T _ | Neq _ | Bool _ -> batset
  | And fs | Or fs -> 
    let rec extract_list fs batset =
      match fs with
      | hd::tl -> 
        let batset = extract_size hd batset in
          extract_list tl batset
      | [] -> batset in
      extract_list fs batset
  | Not f -> extract_size f batset
  | Imply (f1, f2) | Iff (f1, f2) ->
    let batset = extract_size f1 batset in 
      extract_size f2 batset
  
let solve : formula -> int list
=fun f ->
  let batset = BatSet.Int.empty in
  let batset = extract_size f batset in
  let size = BatSet.Int.fold (fun _ acc -> acc + 1) batset 0 in
  let f = trans f in
  let _, model_opt = Solver.check_satisfiability [f] in
  match model_opt with
    | Some model -> 
      let lst = model2solution model size in
      let rec process_lst lst = 
        match lst with
        | hd::tl -> 
          if hd = -1 then process_lst tl else hd :: (process_lst tl)
        | [] -> [] in
        process_lst lst
    | None -> []
  
let cover : sets -> int list  
=fun (n, m, t) -> 
  let encoded_f = encode (n, m, t) in
    solve encoded_f


