open Utils 
(*** Do not open anything else ***)

type var = string  



(*** Propositional Formulas ***)
type formula = 
  | False 
  | True 
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
    | Not f -> "(not " ^ string_of_formula f ^ ")"
    | And (f1, f2) -> "(" ^ string_of_formula f1 ^ " and " ^ string_of_formula f2 ^ ")"
    | Or (f1, f2) -> "(" ^ string_of_formula f1 ^ " or " ^ string_of_formula f2 ^ ")"
    | Imply (f1, f2) -> "(" ^ string_of_formula f1 ^ " -> " ^ string_of_formula f2 ^ ")"
    | Iff (f1, f2) -> "(" ^ string_of_formula f1 ^ " <-> " ^ string_of_formula f2 ^ ")"
  
(*** CNF ***)
type literal = bool * var (* false means negated *)
type clause = literal list 
type cnf = clause list 

let string_of_literal (b, x) = if b then x else "!" ^ x 
let string_of_clause c = string_of_list string_of_literal c ~first:"(" ~last:")" ~sep:"\\/"
let string_of_cnf a = string_of_list string_of_clause a ~first:"(" ~last:")" ~sep:"/\\"
  
(*** DPLL ***)
exception Not_implemented 
exception No_variable_match

(* Problem 1: CNF conversion *)
let represent : formula -> formula
=fun f ->
  match f with
  | True -> True
  | False -> False
  | Var x -> 
    if x = "true" then Var "var_true"
    else 
      if x = "false" then Var "var_false"
      else f
  | _ -> 
    let new_var = "P" in
      Var (new_var ^ string_of_formula f)

let rec encode : formula -> cnf
=fun f ->
  match f with
  | True -> []
  | False -> []
  | Var _ -> []
  | Not f1 -> 
    let program = represent f in
    let rep_f1 = represent f1 in
    let encoded_cnf = encode f1 in
      [
        [(false, string_of_formula program); (false, string_of_formula rep_f1)]; 
        [(true, string_of_formula program); (true, string_of_formula rep_f1)]
      ] @ encoded_cnf
  | Or (f1, f2) ->  
    let program = represent f in
    let rep_f1 = represent f1 in
    let rep_f2 = represent f2 in
    let encoded_cnf1 = encode f1 in
    let encoded_cnf2 = encode f2 in
      [
        [(false, string_of_formula program); (true, string_of_formula rep_f1); (true, string_of_formula rep_f2)];
        [(false, string_of_formula rep_f1); (true, string_of_formula program)];
        [(false, string_of_formula rep_f2); (true, string_of_formula program)]
      ] @ encoded_cnf1 @ encoded_cnf2
  | And (f1, f2) -> 
    let program = represent f in
    let rep_f1 = represent f1 in
    let rep_f2 = represent f2 in
    let encoded_cnf1 = encode f1 in
    let encoded_cnf2 = encode f2 in
      [
        [(false, string_of_formula program); (true, string_of_formula rep_f1)];
        [(false, string_of_formula program); (true, string_of_formula rep_f2)];
        [(false, string_of_formula rep_f1); (false, string_of_formula rep_f2); (true, string_of_formula program)]
      ] @ encoded_cnf1 @ encoded_cnf2
  | Imply (f1, f2) -> 
    let program = represent f in
    let rep_f1 = represent f1 in
    let rep_f2 = represent f2 in
    let encoded_cnf1 = encode f1 in
    let encoded_cnf2 = encode f2 in
      [
        [(false, string_of_formula program); (false, string_of_formula rep_f1); (true, string_of_formula rep_f2)];
        [(true, string_of_formula rep_f1); (true, string_of_formula program)];
        [(false, string_of_formula rep_f2); (true, string_of_formula program)]
      ] @ encoded_cnf1 @ encoded_cnf2
  | Iff (f1, f2) ->
    let program = represent f in
    let rep_f1 = represent f1 in
    let rep_f2 = represent f2 in
    let encoded_cnf1 = encode f1 in
    let encoded_cnf2 = encode f2 in
      [
        [(false, string_of_formula program); (false, string_of_formula rep_f1); (true, string_of_formula rep_f2)];
        [(false, string_of_formula program); (true, string_of_formula rep_f1); (false, string_of_formula rep_f2)];
        [(true, string_of_formula program); (false, string_of_formula rep_f1); (false, string_of_formula rep_f2)];
        [(true, string_of_formula program); (true, string_of_formula rep_f1); (true, string_of_formula rep_f2)]
      ] @ encoded_cnf1 @ encoded_cnf2
      
let convert : formula -> cnf
=fun f ->
  match f with
  | True -> []
  | False -> [[]]
  | Var _ -> 
    let f = represent f in
      [[(true, string_of_formula f)]]
  | Not f1 -> 
    let program = represent f in
    let encoded_f = encode f in
    let encoded_f1 = encode f1 in
      [[(true, string_of_formula program)]] @ encoded_f @ encoded_f1
  | And _ | Or _ | Iff _ | Imply _ ->
    let program = represent f in
    let encoded_f = encode f in
      [[(true, string_of_formula program)]] @ encoded_f

let rec resolve_iter : clause -> (clause * bool)
=fun c ->
  match c with
  | (b, v)::tl ->
    (
      match (b, v) with
      | (true, "true") | (false, "false") -> 
        ([], true)
      | (false, "true") | (true, "false") -> 
        let (c1, b1) = resolve_iter tl in
          if c1 = [] && b1 = true then ([], true)
          else (c1, false)
      | _ -> 
        let (c1, b1) = resolve_iter tl in
          if c1 = [] && b1 = true then ([], true)
          else ([b, v] @ c1, false)
    )
  | [] -> ([], false)

let rec resolve : cnf -> cnf
=fun c ->
  match c with
  | hd::tl ->
    let (c1, b1) = resolve_iter hd in
    if c1 = [] && b1 = true then resolve tl
    else 
      c1 :: (resolve tl)
  | [] -> []



(* Problem 2: substitution a[v/x] (replacing x by v in a) *)
let resolve_literal : literal -> bool -> var -> bool (* (b, v1) , bool of v1 -> result *)
=fun l b v ->
  match l with
  | (true, v1) -> 
    let _ = if v <> v1 then raise No_variable_match in
      if b == true then true else false
  | (false, v1) -> 
    let _ = if v <> v1 then raise No_variable_match in
      if b == true then false else true

let rec resolve_clause : clause -> bool -> var -> (clause * bool)
=fun c b v ->
  match c with
  | (b1, v1)::tl ->
    if v = v1 then
      if resolve_literal (b1, v1) b v then ([], true)
      else 
        resolve_clause tl b v
    else
      let (c2, b2) = resolve_clause tl b v in
        if b2 = true then ([], true)
        else ([(b1, v1)] @ c2, false)
  | [] -> ([], false)

let rec subst_rec : cnf -> bool -> var -> cnf 
=fun a v x -> 
  match a with
  | hd::tl -> 
    let c, b = resolve_clause hd v x in
      if c = [] && b = true then (subst_rec tl v x)
      else [c] @ (subst_rec tl v x)
  | [] -> []

let subst : cnf -> bool -> var -> cnf
=fun a v x ->
  subst_rec a v x


(* Problem 3: boolean constraint propagation *)
let rec find_unit_literal : cnf -> clause
=fun c ->
  let unit_list = [] in
  match c with
  | hd::tl -> 
    if List.length hd = 1 then 
      (
        match hd with
        | h::_ -> unit_list @ [h] @ find_unit_literal tl
        | [] -> []
      )
    else unit_list @ find_unit_literal tl
  | [] -> unit_list

let rec bcp_subst : cnf -> clause -> cnf
=fun c unit_list ->
  match unit_list with
  | (b, v)::tl ->
    let cnf = subst c b v in
      bcp_subst cnf tl
  | [] -> c

let rec bcp_sub : cnf -> clause -> cnf
=fun c unit_list ->
  let unit_list_add = find_unit_literal c in
  let unit_list = unit_list @ unit_list_add in
  let c = resolve c in
    if List.length unit_list_add = 0 then bcp_subst c unit_list
    else let cnf = bcp_subst c unit_list in bcp_sub cnf unit_list

let bcp : cnf -> cnf
=fun c -> 
  let unit_list = [] in
    bcp_sub c unit_list


(* Problem 4: pure literal elimination *)
let rec ple_iter_clause_low : clause -> literal -> bool
=fun c (b, v) ->
  match c with
  | (b1, v1)::tl -> 
    if v = v1 && b <> b1 then 
      false 
    else ple_iter_clause_low tl (b, v)
  | [] -> true

let rec ple_iter_cnf : cnf -> literal -> bool
=fun c (b, v) ->
  match c with
  | hd::tl -> 
    ple_iter_clause_low hd (b, v) && ple_iter_cnf tl (b, v)
  | [] -> true

let rec ple_iter_clause : clause -> cnf -> clause
=fun c total_cnf -> 
  match c with
  | (b, v)::tl ->
    if ple_iter_cnf total_cnf (b, v) then [(b, v)] @ (ple_iter_clause tl total_cnf)
    else ple_iter_clause tl total_cnf
  | [] -> []

let rec find_unique_literal : cnf -> cnf -> clause 
=fun c total_cnf ->
  match c with
  | hd::tl ->
    ple_iter_clause hd total_cnf @ find_unique_literal tl total_cnf
  | [] -> []

let rec ple_subst : cnf -> clause -> cnf
=fun c unique_list ->
  match unique_list with
  | (b, v)::tl -> 
    let c = resolve c in
    let resolved_cnf = subst c b v in
      ple_subst resolved_cnf tl
  | [] -> c

let rec ple : cnf -> cnf 
=fun c -> 
  let unique_list = find_unique_literal c c in
  if List.length unique_list = 0 then c
  else
    let cnf = ple_subst c unique_list in ple cnf

let choose : cnf -> var 
=fun a -> snd (List.hd (List.hd a))

let rec dpll : cnf -> bool 
=fun a ->  
  let a = ple (bcp a) in 
    if a = [] then true  (* /\ [] = true *)
    else if List.mem [] a then false (* \/ [] = false *)
    else 
      let x = choose a in 
        dpll (subst a false x) || dpll (subst a true x) 

let solve : formula -> bool 
=fun f -> dpll (convert f)
