open Smt
open Utils 

type pgm = var list * lib list * var 
and lib = var * var list * var * phi 
and var = string 
and phi = EQ of exp * exp 
and exp = 
  | INT of int 
  | VAR of var 
  | ADD of exp * exp  
  | MUL of exp * exp  

type spec = int list * int 

let string_of_pgm (invars, libs, outvar) = 
  (* let _ = print_string (string_of_int (List.length invars) ^ "\n\n") in *)
  "def f(" ^ string_of_list id invars ~first:"" ~last:"" ^ "): " ^ "\n" ^
  list_fold (fun (name, ins, out, _) s -> 
    s ^ "  " ^ out ^ " := " ^ name ^ string_of_list id ins ^ "\n"
  ) libs "" ^ 
  "  return " ^ outvar ^ "\n"

let rec string_of_exp : exp -> string
=fun e ->
  match e with
  | INT n -> string_of_int n
  | VAR v -> v
  | ADD (e1, e2) -> (string_of_exp e1) ^ " " ^ (string_of_exp e2)
  | MUL (e1, e2) -> (string_of_exp e1) ^ " " ^ (string_of_exp e2)

let string_of_phi (EQ (e1, e2)) =
  (string_of_exp e1) ^ " = " ^ (string_of_exp e2)

type const = 
  | EQP of phi 
  | EXP of exp
  | AND of const list
  | EQUAL of const * const

let rec trans : const -> Fmla.t
=fun c -> 
  match c with
  | EQP p -> 
    (
      match p with
      | EQ (e1, e2) -> Expr.create_eq (trans (EXP e1)) (trans (EXP e2))
    )
  | EXP e ->
    (
      match e with
      | INT n -> Expr.of_int n
      | VAR v -> Expr.create_var (Expr.sort_of_int()) ~name: v
      | ADD (e1, e2) -> Expr.create_add (trans (EXP e1)) (trans (EXP e2))
      | MUL (e1, e2) -> Expr.create_mul (trans (EXP e1)) (trans (EXP e2))
    )
  | AND cl -> Fmla.create_and (List.map trans cl)
  | EQUAL (c1, c2) -> Expr.create_eq (trans c1) (trans c2)

let get_phi : lib -> phi
=fun (_, _, _, phi) -> phi

let get_hd : 'a list -> 'a
=fun lst ->
  match lst with
  | hd::_ -> hd
  | _ -> raise (Failure "FAIL")

let bigand f l = AND (List.map f l)

let rec extract_all_phi : lib list -> phi list
=fun ll ->
  match ll with
  | hd::tl -> 
    (get_phi hd)::extract_all_phi tl
  | [] -> []


let model2solution : Model.t -> var list -> var -> string list * string
=fun model vl z ->
  let sl1 = 
  List.map ( fun i ->
    let v = Expr.create_var (Expr.sort_of_int()) ~name: (List.nth vl i) in
    match Model.eval v ~model:model with
    | Some expr ->
      Expr.to_string expr
    | _ -> raise (Failure "FAIL")
  ) (range (List.length vl)) in
  let sl2 = 
    let v = Expr.create_var (Expr.sort_of_int()) ~name: z in
    match Model.eval v ~model:model with
    | Some expr ->
      Expr.to_string expr
    | _ -> raise (Failure "FAIL") in
  (sl1, sl2)

let check_match : spec -> string list -> string -> bool
=fun (nl, n) sl s ->
  let rec check_match_by_elm : string list -> int -> bool
  =fun sl n ->
    match sl with
    | hd::tl ->
      if (int_of_string hd) <> n then false else check_match_by_elm tl n
    | [] -> true
  in
  let rec check_match_sub : int list -> string list -> bool
  =fun nl sl ->
    if List.length nl <> List.length sl then
      if check_match_by_elm sl (get_hd nl) then true
      else false
    else 
    (
      match nl, sl with
      | h1::t1, h2::t2 ->
        if h1 <> (int_of_string h2) then false 
        else check_match_sub t1 t2
      | [], [] -> true
      | _ -> raise (Failure "FAIL")
    )
  in 
  let b1 = check_match_sub nl sl in
    b1 && (n = (int_of_string s))


let verify_sub : pgm -> phi list -> spec -> bool
=fun (vl, _, v) pl (nl, n) ->
  let cst = 
    AND [
      (
        if List.length vl <> List.length nl then 
        bigand ( fun i ->
          EQUAL (EXP (VAR (List.nth vl i)), EXP (INT (List.nth nl 0)))
        ) (range (List.length vl))
      else
        bigand ( fun i ->
          EQUAL (EXP (VAR (List.nth vl i)), EXP (INT (List.nth nl i)))
        ) (range (List.length vl))
      );
        bigand ( fun i ->
          EQP (List.nth pl i)
        ) (range (List.length pl));
        EQUAL (EXP (VAR v), EXP (INT n))
    ] in
  let f = trans cst in
  let _, model_opt = Solver.check_satisfiability [f] in
  match model_opt with
  | Some model -> 
    let (sl, s) = model2solution model vl v in
      check_match (nl, n) sl s
  | None -> false
  

let verify : pgm -> spec -> bool
=fun (vl, ll, v) spec -> 
  (*
    pgm = var list * lib list * var
    =>
    (
    ["x"],
      [
       ("add", ["x"; "x"], "y", EQ (VAR "y", ADD (VAR "x", VAR "x")));
       ("mul", ["y"; "y"], "z", EQ (VAR "Z", MUL (VAR "y", VAR "y")))
      ],
    "z"
    )   
  *)
  (*
    spec = int list * int
    => ([2], 16) 
    => input 인자들 -> 결과값   
  *)
  (*
    z3 solver가 사용할 수 있도록 변환해준다음에 check_sat 을 이용해 SAT 판별  
    -> 해를 전부 모아놓고 해당 "해집합"에 입출력 명세가 존재하는지 확인 

    -> sort of int로 int형 변수를 만듦. 현재식과 다음식을 연결하는방법은?

    -> 이 단계에서 "mul", ["x0"; "x2"], "o1" 은 print_pgm할 때 필요함 / 그냥 맨 뒤에꺼만 생각
  *)
  let _ = print_string (string_of_pgm (vl, ll, v)) in
  let phi_list = extract_all_phi ll in
    verify_sub (vl, ll, v) phi_list spec

(*
******************************************************************************
*)

type lx = string
and program =
  | EXP of exp
  | EQP of phi 
  | INT of int
  | AND of program list
  | EQUAL of program * program
  | GT of program * program
  | GTE of program * program
  | NEQ of program * program
  | IMPLY of program * program
  | LINE of lx
  | I' of int
  | I of int * int
  | O of int
  | START of int
  | END

let bigand f l = AND (List.map f l)

let rec trans : program -> Fmla.t
=fun p ->
  match p with
  | EXP e ->
    (
      match e with
      | INT n -> Expr.of_int n
      | VAR v -> Expr.create_var (Expr.sort_of_int()) ~name: v
      | ADD (e1, e2) -> Expr.create_add (trans (EXP e1)) (trans (EXP e2))
      | MUL (e1, e2) -> Expr.create_mul (trans (EXP e1)) (trans (EXP e2))
    )
  | EQP p -> 
    (
      match p with
      | EQ (e1, e2) -> Expr.create_eq (trans (EXP e1)) (trans (EXP e2))
    )
  | INT n -> Expr.of_int n
  | AND pl -> Fmla.create_and (List.map trans pl)
  | EQUAL (p1, p2) -> Expr.create_eq (trans p1) (trans p2)
  | GT (p1, p2) -> Expr.create_gt (trans p1) (trans p2)
  | GTE (p1, p2) -> Expr.create_ge (trans p1) (trans p2)
  | NEQ (p1, p2) -> Expr.create_neq (trans p1) (trans p2)
  | IMPLY (p1, p2) -> Fmla.create_imply (trans p1) (trans p2)
  | LINE v -> Expr.create_var (Expr.sort_of_int()) ~name: ("l_" ^ v)
  | I' n -> Expr.create_var (Expr.sort_of_int()) ~name: ("i" ^ string_of_int n)
  | I (n1, n2) -> Expr.create_var (Expr.sort_of_int()) ~name: ("i" ^ string_of_int n1 ^ string_of_int n2)
  | O n -> Expr.create_var (Expr.sort_of_int()) ~name: ("o" ^ string_of_int n)
  | START n -> Expr.create_var (Expr.sort_of_int()) ~name: ("S" ^ string_of_int n)
  | END -> Expr.create_var (Expr.sort_of_int()) ~name: "E"

let rec extract_io : lib list -> var list -> var list -> (var list * var list)
=fun ll ilst olst ->
  match ll with
  | (_, ins, out, _)::tl ->
    extract_io tl (ilst@ins) (olst@[out]) 
  | [] -> (ilst, olst)

let get_fname : lib -> var
=fun (fname, _, _, _) -> fname
let get_inputs : lib -> var list 
=fun (_, inputs, _, _) -> inputs
let get_out : lib -> var
=fun (_, _, out, _) -> out

let encode_wfp : lib list -> lx list -> lx list -> int list -> program
=fun ll ilst olst v1 ->
  let c1 = 
    AND [
      bigand ( fun i ->
        EQUAL (LINE ("S" ^ (string_of_int i)), INT (-1*i));
      ) (range (List.length v1));
      EQUAL (LINE "E", INT (List.length ll));
      bigand ( fun i ->
        AND [
          GTE (LINE (List.nth ilst i), INT ((-1*(List.length v1))+1));
          GTE (INT (List.length ll), LINE (List.nth ilst i))
        ]
      ) (range (List.length ilst));
      bigand ( fun i ->
        AND [
          GTE (LINE (List.nth olst i), INT 1);
          GTE (INT (List.length ll), LINE (List.nth olst i))
        ]
      ) (range (List.length olst))
    ] 
  in
  let c2 = 
    bigand ( fun i ->
      bigand ( fun j ->
        IMPLY (
          NEQ (INT i, INT j), 
          NEQ (LINE (List.nth olst i), LINE (List.nth olst j))
        )
      ) (range (List.length olst))
    ) (range (List.length olst)) in
  let c3 = 
    bigand ( fun i ->
      let inputs = get_inputs (List.nth ll i) in
      bigand ( fun j ->
        GT (LINE (List.nth olst i), LINE (List.nth inputs j))
      ) (range (List.length inputs))
    ) (range (List.length ll)) in 
  AND [c1; c2; c3]

let str2program : string -> program
=fun s ->
  match String.get s 0 with
  | 'i' -> 
    (
      try 
        let r1 = String.get s 1 in 
        let r2 = String.get s 2 in
          I (int_of_string (Char.escaped r1), int_of_string (Char.escaped r2))
      with
      | Invalid_argument _ -> 
        let r1 = String.get s 1 in 
          I' (int_of_string (Char.escaped r1))
      | _ -> raise (Failure "FAIL in str2program")
    )
  | 'o' -> 
    let r = String.get s 1 in
      O (int_of_string (Char.escaped r))
  | _ -> raise (Failure "FAIL in str2program")
  

let encode_conn : lx list -> lx list -> int list -> program
=fun ilst olst v1 ->
  let s_lst = List.mapi (fun i _ -> "S" ^ string_of_int i) v1 in
  let str_lst = (ilst @ olst @ s_lst @ ["E"]) in
  let lst = List.map str2program (ilst @ olst) in
  let start_lst = List.mapi (fun i _ -> START i) v1 in
  let lst = lst @ start_lst @ [END] in 
  bigand ( fun i ->
    bigand ( fun j ->
      IMPLY (
        EQUAL (LINE (List.nth str_lst i), LINE (List.nth str_lst j)),
        EQUAL (List.nth lst i, List.nth lst j)
      )
    ) (range (List.length lst))
  ) (range (List.length lst))


let encode_lib : lib list -> program
=fun ll ->
  bigand ( fun i ->
    let phi = get_phi (List.nth ll i) in
      EQP (phi)
  ) (range (List.length ll))


let encode_io : int list -> int -> program
=fun v1 v2 -> 
  AND [
    bigand ( fun i ->
      EQUAL (START i, INT (List.nth v1 i))
    ) (range (List.length v1));
    EQUAL (END, INT v2)
  ]

(*///////////////////////////////////////////////////////////////////////*)

let sort_by_lnum lst =
  let compare_lnum (_, lnum_a) (_, lnum_b) =
    compare lnum_a lnum_b
  in
  List.sort compare_lnum lst

let rec remove_lnum lst =
  match lst with
  | (lib, _)::tl -> 
    lib :: (remove_lnum tl)
  | [] -> []

let get_liblst_hd lst =
  match lst with
  | hd::_ -> hd
  | [] -> raise (Failure "No Head")

let rec replace_io_ins : lx list -> lx -> lx list 
=fun ll out -> 
  match ll with
  | _::tl -> [out]@(replace_io_ins tl out)
  | _ -> []

let rec replace_io_phi : phi -> lx -> phi
=fun phi out ->
  match phi with
  | EQ (e1, e2) ->
    EQ (replace_io_exp e1 out, replace_io_exp e2 out)
and replace_io_exp : exp -> lx -> exp
=fun exp out -> 
  match exp with
  | INT n -> INT n
  | VAR v -> 
    (
      match String.get v 0 with
      | 'i' -> VAR out
      | _ -> VAR v
    )
  | ADD (e1, e2) -> ADD (replace_io_exp e1 out, replace_io_exp e2 out)
  | MUL (e1, e2) -> MUL (replace_io_exp e1 out, replace_io_exp e2 out)

let match_io : lib -> lx -> lib
=fun (fname, ins, o, phi) out ->
  let new_ins = replace_io_ins ins out in
  let new_phi = replace_io_phi phi out in
    (fname, new_ins, o, new_phi)

(*///////////////////////////////////////////////////////////////////////*)
  
let rec print_string_list = function
  | [] -> ()
  | head :: tail ->
      print_endline head;
      print_string_list tail

let model2solution : Model.t -> int list -> lib list -> lx list -> lx list -> pgm
=fun model v1 ll ilst olst ->  ignore v1;
  let model_ilst = 
    (* 라인이 같은애들은 같은 변수명으로 바꿔주는 작업 *)
    (* 문제가 ilst 를 이용해서 구해서 생기는거같음. ilst대신 v1으로 하면..? *)
    List.map ( fun i -> 
      let v = Expr.create_var (Expr.sort_of_int()) ~name: ("l_" ^ (List.nth ilst i)) in
      match Model.eval v ~model:model with
      | Some expr ->
        if Expr.to_string expr = "0" || String.get (Expr.to_string expr) 0 = '(' then List.nth ilst i
        else "-1"
      | None -> raise (Failure "FAIL in model_ilst")
    ) (range (List.length ilst)) in
  let rec process_lst : lx list -> lx list
  =fun ilst -> 
    match ilst with
    | hd::tl ->
      if hd = "-1" then process_lst tl else hd :: (process_lst tl)
    | [] -> [] 
  in
  let model_ilst = (process_lst model_ilst) in
  let _ = print_string (string_of_int (List.length model_ilst) ^ "\n") in
  let model_olst = 
    List.map ( fun i ->
      let v = Expr.create_var (Expr.sort_of_int()) ~name: ("l_" ^ List.nth olst i) in
      match Model.eval v ~model:model with
      | Some expr ->
        if Expr.to_string expr = (string_of_int (List.length ll)) then List.nth olst i
        else "-1"
      | None -> raise (Failure "FAIL in model_olst")
  ) (range (List.length olst)) in
  let model_olst = (process_lst model_olst) in
  let pair_ll = 
    List.map( fun i -> 
      let out = get_out (List.nth ll i) in
      let v = Expr.create_var (Expr.sort_of_int()) ~name: out in
      match Model.eval v ~model:model with
      | Some expr ->
        if String.get (Expr.to_string expr) 0 = '(' then
         (List.nth ll i, 0)
        else 
         (List.nth ll i, int_of_string (Expr.to_string expr))
      | None -> raise (Failure "FAIL in pair_ll")
    ) (range (List.length ll)) in
  let ordered_ll = remove_lnum (sort_by_lnum pair_ll) in
  (
    model_ilst, ordered_ll, (List.nth model_olst 0)
  )
  

let synthesize : lib list -> spec -> pgm option 
=fun ll (v1, v2) -> 
  let ilst, olst = extract_io ll [] [] in
  let wfp_const = encode_wfp ll ilst olst v1 in
  let conn_const = encode_conn ilst olst v1 in
  let lib_const = encode_lib ll in
  let io_const = encode_io v1 v2 in
  let f = trans (AND [wfp_const; conn_const; lib_const; io_const]) in
  let _, model_opt = Solver.check_satisfiability [f] in
  match model_opt with
    | Some model -> 
      let _ = print_string (Model.to_string model ^ "\n") in
      let pgm = model2solution model v1 ll ilst olst in 
      Some pgm
    | None -> None



let rec lib_change_pairs : lib -> (var * var) list -> lib
=fun (name, input_vars, output_var, EQ(phi_e1, phi_e2)) change_pairs -> 
  let rec change_exp : var * var -> exp -> exp
  =fun (orig_var, new_var) e -> 
    match e with
    | INT n -> INT n
    | VAR x -> if x = orig_var then VAR new_var else VAR x
    | ADD (e1, e2) -> ADD (change_exp (orig_var, new_var) e1, change_exp (orig_var, new_var) e2)
    | MUL (e1, e2) -> MUL (change_exp (orig_var, new_var) e1, change_exp (orig_var, new_var) e2)
  in 
  match change_pairs with
  | [] -> (name, input_vars, output_var, EQ(phi_e1, phi_e2))
  | (orig_in, new_in)::tl -> 
    lib_change_pairs (name, List.map (fun x -> if x = orig_in then new_in else x) input_vars, output_var, 
    EQ(change_exp (orig_in, new_in) phi_e1, change_exp (orig_in, new_in) phi_e2)) tl  