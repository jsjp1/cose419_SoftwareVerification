open Utils 
open Smt 

type specification = int * int * example list * example list 
and example = int list 

let spec1 = (10, 2, 
[
  [0; 1]; 
  [1; 0]
], 
[
  [1; 1]; 
  [0; 0]
])

let spec2 = (10, 2, 
[
  [1; 1]
], 
[
  [0; 1]; 
  [1; 0]; 
  [0; 0]
])

let spec3 = (10, 3, 
[
  [0;0;0]; 
  [0;1;0];
  [1;0;0];
  [1;1;0];
], 
[
  [0;0;1]; 
  [0;1;1];
  [1;0;1];
  [1;1;1];
])

let spec4 = (10, 4, 
[
  [0;0;0;1]; 
  [0;0;1;1];
  [0;1;0;1];
  [1;0;0;1];
  [1;0;1;1];
  [1;1;0;1];
  [1;1;1;0];
], 
[
  [0;0;0;0];
  [0;0;1;0];
  [0;1;0;0];
  [0;1;1;0];
  [0;1;1;1];
  [1;0;0;0];
  [1;0;1;0];
  [1;1;0;0];
])

let spec5 = (20, 20, 
[
  [1;1;0;0;1;0;0;1;0;0;0;0;1;1;1;1;1;1;0;1];
  [1;0;1;0;1;0;1;0;0;0;1;0;0;0;1;0;0;0;0;1];
  [0;1;1;0;1;0;0;0;1;1;0;0;0;0;1;0;0;0;1;1];
  [0;1;0;0;1;1;0;0;0;1;0;0;1;1;0;0;0;1;1;0];
  [0;1;1;0;0;0;1;0;1;0;0;0;1;0;1;1;1;0;0;0];
  [0;0;0;0;1;1;0;1;1;1;0;0;0;0;0;1;1;1;0;0];
  [1;1;0;1;0;0;0;1;0;0;1;0;1;0;0;1;0;0;0;0];
  [0;0;1;0;0;1;0;0;1;1;1;0;0;0;0;0;1;0;0;0];
  [1;0;0;0;1;0;1;0;0;1;1;0;0;1;1;1;1;1;0;0];
  [1;1;0;0;0;1;1;1;0;1;0;0;0;0;0;0;0;0;1;0];
  [0;0;0;0;1;0;1;1;1;0;1;1;1;1;1;0;1;0;1;0];
  [0;1;1;0;0;0;1;1;1;0;1;1;0;0;0;1;0;0;1;1];
  [1;0;0;1;1;0;1;1;0;0;1;0;0;0;1;0;0;1;0;1];
  [0;0;0;1;0;1;0;0;1;0;1;0;0;0;0;0;1;0;0;0];
  [0;1;1;1;1;0;0;1;1;0;0;0;1;1;1;0;0;0;1;1];
  [0;1;0;0;0;0;0;0;0;1;0;0;1;1;0;1;1;1;0;1];
], 
[
  [1;0;1;0;1;1;0;1;1;1;1;1;1;0;0;0;0;1;0;1];
  [0;1;0;0;0;1;0;1;1;0;0;0;1;0;1;0;0;0;1;0];
  [1;0;1;1;1;0;1;1;0;1;0;0;1;0;1;0;1;0;0;1];
  [1;0;1;0;1;0;1;0;1;1;1;1;1;1;0;1;1;1;0;0];
  [0;1;0;1;0;1;1;0;0;0;1;0;0;0;0;0;0;0;1;0];
  [0;1;1;1;0;0;1;1;1;1;0;1;0;0;1;1;1;1;0;0];
  [1;1;1;1;0;0;0;1;1;1;0;1;1;0;0;0;1;0;1;1];
  [1;0;0;1;1;1;0;0;0;1;0;1;1;0;0;0;0;0;1;1];
  [1;1;0;0;1;1;1;0;0;0;1;0;1;1;0;1;0;0;1;1];
  [0;1;1;0;1;0;0;1;0;1;0;1;1;0;1;0;1;0;0;1];
  [1;1;1;0;0;0;0;1;0;0;1;1;0;1;1;0;0;1;0;0];
  [0;0;0;1;0;0;0;1;0;1;0;0;0;1;1;0;0;1;0;0];
  [0;0;1;1;0;0;1;1;1;1;1;1;1;0;1;1;1;1;0;0];
  [1;1;0;0;1;0;0;1;0;0;1;1;1;0;0;1;1;1;0;1];
  [1;1;0;0;1;1;1;0;0;0;1;0;0;1;0;0;1;0;0;1];
  [1;0;1;1;0;0;1;1;1;1;1;0;1;1;1;1;1;0;0;1];
])

let spec11 = (
  100, 2, 
  [
  [0;0];
  [0;1]
], []
)

type dnf = conj list (* [[x1; x2; x3]; [x1; x2; x3]; ...] *)
and conj = lit list (* [x1; x2; x3] *)
and lit = X of int | NotX of int  (* x1 *)

type const =
  | P of (int * int)
  | Q of (int * int)
  | Z of (int * int)
  | Bool of bool
  | And of const list
  | Or of const list
  | Not of const

let string_of_lit lit = 
  match lit with 
  | X i -> "x" ^ string_of_int i 
  | NotX i -> "!x" ^ string_of_int i 
let string_of_conj conj = string_of_list string_of_lit conj ~sep:" /\\ " ~first:"(" ~last:")"
let string_of_dnf dnf = string_of_list string_of_conj dnf ~sep:" \\/ " ~first:"" ~last:""


let bigand f l = And (List.map f l)
let bigor f l = Or (List.map f l)

let rec trans : const -> Fmla.t
=fun c -> 
  match c with
  | P (n1, n2) -> Expr.create_var (Expr.sort_of_bool()) ~name: ("p" ^ string_of_int n1 ^ "_" ^ string_of_int n2)
  | Q (n1, n2) -> Expr.create_var (Expr.sort_of_bool()) ~name: ("q" ^ string_of_int n1 ^ "_" ^ string_of_int n2)
  | Z (n1, n2) -> Expr.create_var (Expr.sort_of_bool()) ~name: ("z" ^ string_of_int n1 ^ "_" ^ string_of_int n2)
  | Bool b -> 
    (
      match b with
      | true -> Expr.true_ ()
      | false -> Expr.false_ ()
    )
  | And cl -> Fmla.create_and (List.map trans cl)
  | Or cl -> Fmla.create_or (List.map trans cl)
  | Not c -> Fmla.create_not (trans c)

let rec get_data_from_example example cur index = 
  match example with
  | hd::tl ->
    if cur = index then hd else get_data_from_example tl (cur+1) index
  | [] -> -1

let pos_const_by_example : example -> int -> int -> int -> const
=fun ex cur_m ex_cnt n ->
  let c1 = bigor ( fun i ->
    Z (i, ex_cnt)
  ) (range cur_m) in
  let c2 = bigand ( fun i ->
    bigand ( fun j ->
      let q_or_p = 
        if get_data_from_example ex 0 j = 1 then Q (i, j) else P (i, j)
      in
        Or [
          Not (Z (i, ex_cnt));
          Not q_or_p
        ]
    ) (range n)
  ) (range cur_m) in 
  And [c1; c2]

let rec pos_const : example list -> int -> int -> int -> const
=fun el cur_m ex_cnt n ->
  match el with
  | hd::tl ->
    let a = pos_const_by_example hd cur_m ex_cnt n in
    And [
      a; pos_const tl cur_m (ex_cnt+1) n
    ]
  | [] -> Bool true

let neg_const_by_example : example -> int -> const
=fun ex cur_m ->
  bigand ( fun i ->
    bigor ( fun j ->
      if get_data_from_example ex 0 j = 1 then Q (i, j) else P (i, j)
    ) (range (List.length ex))
  ) (range cur_m)

let rec neg_const : example list -> int -> const
=fun el cur_m ->
  match el with
  | hd::tl ->
    let a = neg_const_by_example hd cur_m in
    And [
      a; neg_const tl cur_m
    ]
  | [] -> Bool true

let model2solution : Model.t -> int -> int -> dnf
=fun model n cur_m -> 
  let dnf = 
    List.map (fun i ->
      List.map ( fun j ->
        let p = Expr.create_var (Expr.sort_of_bool()) ~name: ("p" ^ string_of_int i ^ "_" ^ string_of_int j) in
        let q = Expr.create_var (Expr.sort_of_bool()) ~name: ("q" ^ string_of_int i ^ "_" ^ string_of_int j) in
        match Model.eval p ~model:model, Model.eval q ~model:model with
        | Some expr1, Some expr2 -> 
          if Expr.to_string expr1 = "true" then X (j+1)
          else 
            if Expr.to_string expr2 = "true" then NotX (j+1)
            else X (-1)
        | _-> raise (Failure "QQQ")
      ) (range n)
    ) (range cur_m) in dnf

let rec loop : specification -> int -> dnf option
=fun (max_m, n, pos, neg) cur_m -> 
  let c_p = pos_const pos cur_m 0 n in
  let c_n = neg_const neg cur_m in
  let f = trans (And [c_p; c_n]) in
  let _, model_opt = Solver.check_satisfiability [f] in
    match model_opt with
    | Some model ->
      (* let _ = prerr_endline (Model.to_string model) in *)
      let dnf = model2solution model n cur_m in
        Some dnf
    | None -> 
      if (cur_m + 1) <= max_m then
        loop (max_m, n, pos, neg) (cur_m + 1) 
      else None

let synthesize : specification -> dnf option  
=fun spec ->
  let dnf_option = loop spec 0 in
  match dnf_option with
  | Some dnf ->
    let rec process_dnf dnf =
      (
        match dnf with
        | hd::tl -> 
          let rec process_conj conj = 
            (
              match conj with
              | (X n1)::tl ->
                if n1 = -1 then process_conj tl else (X n1)::(process_conj tl)
              | (NotX n1)::tl ->
                (NotX n1)::(process_conj tl)
              | [] -> []
            ) in
            (process_conj hd) :: (process_dnf tl)
        | [] -> []
      )
      in
    let processed_dnf = process_dnf dnf in Some processed_dnf
  | None -> None