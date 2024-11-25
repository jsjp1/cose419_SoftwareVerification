open Syntax
(* open Graph *)
open Utils
open Smt 


let rec generate_lst : int -> int -> int list
=fun start ed ->
  if start <= ed then [start]@(generate_lst (start+1) ed)
  else []

let get_hd lst = match lst with | hd::_ -> hd | [] -> raise (Failure "List length must be >= 1 to get hd")

let get_tl lst = match lst with | _::tl -> tl | [] -> raise (Failure "List length must be >= 1 to get tl")

let replace_hd lst el =
  match lst with
  | _::tl -> el::tl
  | [] -> []

let rec replace_last lst el =
  match lst with
  | [] -> raise (Failure "Empty list")
  | [_] -> [el]
  | hd::tl -> hd::(replace_last tl el) 

let rec remove_last lst =
  match lst with
  | [] -> raise (Failure "Empty list")
  | [_] -> []
  | hd::tl -> hd::(remove_last tl) 

let rec get_last_el lst = 
  match lst with
  | [hd] -> hd 
  | hd::tl -> 
    if List.length tl = 0 then hd else get_last_el tl 
  | [] -> raise (Failure "List length must be >= 1 to get last el") 


let rec reverse_lst lst
=match lst with
  | hd::tl -> (reverse_lst tl)@[hd]
  | [] -> []

let nodeset_lst nodeset = 
  let lst = ref [] in
  Graph.NodeSet.iter (fun node -> lst := !lst @ [node] ) nodeset;
  !lst

let nodeset_size nodeset =
  let cnt = ref 0 in
  Graph.NodeSet.iter (fun _ -> cnt := !cnt + 1) nodeset;
  !cnt

let  print_id_map : (id, typ) BatMap.t -> unit
=fun map ->
  BatMap.iter ( fun id typ ->
    print_string id; print_string ": "; 
    print_string (string_of_typ typ);
    print_string "\n"
  ) map

let print_function_entry : Graph.Cfg.t -> unit
=fun cfg -> print_string (Graph.Node.to_string (Graph.Cfg.get_entry cfg) ^ "\n")

let print_function_exit : Graph.Cfg.t -> unit
=fun cfg -> print_string (Graph.Node.to_string (Graph.Cfg.get_exit cfg) ^ "\n")

let rec print_loopheads_lst : Graph.Node.t list -> unit
=fun lst ->
  match lst with
  | hd::tl -> let _ = print_string (Graph.Node.to_string hd) in print_loopheads_lst tl
  | [] -> ()

let print_fmla : Syntax.fmla -> unit
=fun fmla ->
  print_string (Syntax.string_of_fmla fmla ^ "\n")

let rec print_fmla_lst : Syntax.fmla list -> unit
=fun lst -> 
  match lst with
  | hd::tl -> print_string (Syntax.string_of_fmla hd ^ " -> "); print_fmla_lst tl
  | [] -> ()

let rec print_fmla_lstlst : Syntax.fmla list list -> unit
=fun lst ->
  match lst with
  | hd::tl ->
    print_fmla_lst hd;  
    print_string "\n\n";
    print_fmla_lstlst tl  
  | [] -> ()

let print_exp : exp -> unit
=fun e -> 
  print_string (string_of_exp e ^ "\n")

let rec print_exp_lst : exp list -> unit
=fun lst -> 
  match lst with
  | e::tl -> print_string (string_of_exp e ^ " -> "); print_exp_lst tl
  | [] -> ()

let print_node : Graph.Node.t -> unit
=fun node ->
  print_string (Graph.Node.to_string node ^ "\n")

let rec print_node_lst : Graph.Node.t list -> unit
=fun lst -> 
  match lst with
  | hd::tl -> print_string (Graph.Node.to_string hd ^ " -> "); print_node_lst tl
  | [] -> ()

let rec print_node_lstlst : Graph.Node.t list list -> unit
=fun lst ->
  match lst with
  | hd::tl ->
    print_node_lst hd;  
    print_string "\n";
    print_node_lstlst tl  
  | [] -> ()

let rec print_succs : Graph.Node.t list -> Graph.Cfg.t -> unit
=fun lst cfg -> 
  match lst with
  | hd::tl -> let c = Graph.Cfg.succs hd cfg in
    let _ = print_string (Graph.Node.to_string hd ^ " -> ") in
    let _ = Graph.NodeSet.iter ( fun s ->
      print_endline (string_of_int (Graph.Node.get_nodeid s))
    ) c in
    let _ = print_string "\n" in
    print_succs tl cfg
  | [] -> ()

let rand : int ref = ref 0
let generate_fresh_var : unit -> id
=fun () ->
  let _ = rand := !rand + 1 in
  "rand_" ^ (string_of_int !rand)


let rec trans_exp : Syntax.exp -> (id, typ) BatMap.t -> Fmla.t
=fun exp id_typ_map ->
  match exp with
  | E_int n -> Expr.of_int n
  | E_bool b -> Expr.of_bool b
  | E_lv (V_var id) -> 
    (
    try 
      let typ_of_id = BatMap.find id id_typ_map in
      (
        match typ_of_id with
        | T_int -> 
          Expr.create_var (Expr.sort_of_int()) ~name: id
        | T_bool -> 
          Expr.create_var (Expr.sort_of_bool()) ~name: id
        | T_arr T_int -> 
          Expr.create_var (Expr.sort_of_arr(Expr.sort_of_int())) ~name: id
        | T_arr T_bool ->
          Expr.create_var (Expr.sort_of_arr(Expr.sort_of_bool())) ~name: id
        | _ -> raise (Failure "TODO")
      )
    with Not_found ->
      Expr.create_var (Expr.sort_of_int()) ~name: id
    )
  | E_lv (V_arr (id, e)) -> 
    let typ_of_id = BatMap.find id id_typ_map in
    if typ_of_id = T_arr T_int then
      Expr.read_arr (Expr.create_var (Expr.sort_of_arr(Expr.sort_of_int())) ~name: id) ~idx: (trans_exp e id_typ_map)
    else
      Expr.read_arr (Expr.create_var (Expr.sort_of_arr(Expr.sort_of_bool())) ~name: id) ~idx: (trans_exp e id_typ_map)
  | E_arr_update (id, e1, e2) -> 
    (*
      id -> array 
      e1 -> index (int or v)
      e2 -> value (int or bool or v)
    *)
    let arr = Expr.create_var (Expr.sort_of_arr(Expr.read_sort(trans_exp e2 id_typ_map))) ~name: id in
      Expr.update_arr arr ~idx: (trans_exp e1 id_typ_map) ~value: (trans_exp e2 id_typ_map)
  | E_add (e1, e2) -> Expr.create_add (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)
  | E_sub (e1, e2) -> Expr.create_sub (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)
  | E_mul (e1, e2) -> Expr.create_mul (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)
  | E_div (e1, e2) -> Expr.create_div (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)
  | E_neg e -> Expr.create_neg (trans_exp e id_typ_map)
  | E_len id -> 
    Expr.create_var (Expr.sort_of_int()) ~name: ("|" ^ id ^ "|")
  | E_not e -> Expr.create_not (trans_exp e id_typ_map)
  | E_eq (e1, e2) -> Expr.create_eq (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)
  | E_neq (e1, e2) -> Expr.create_neq (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)
  | E_lt (e1, e2) -> Expr.create_lt (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)
  | E_gt (e1, e2) -> Expr.create_gt (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)
  | E_le (e1, e2) -> Expr.create_le (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)
  | E_ge (e1, e2) -> Expr.create_ge (trans_exp e1 id_typ_map) (trans_exp e2 id_typ_map)

let rec trans_fmla : Syntax.fmla -> (id, typ) BatMap.t -> Fmla.t
=fun fmla id_typ_map ->
  match fmla with
  | F_exp e -> trans_exp e id_typ_map
  | F_order _ -> Fmla.true_()
  | F_not f -> Fmla.create_not (trans_fmla f id_typ_map)
  | F_and fl -> Fmla.create_and (List.map (fun f -> trans_fmla f id_typ_map) fl)
  | F_or fl -> Fmla.create_or (List.map (fun f -> trans_fmla f id_typ_map) fl)
  | F_imply (f1, f2) -> Fmla.create_imply (trans_fmla f1 id_typ_map) (trans_fmla f2 id_typ_map)
  | F_iff (f1, f2) -> Fmla.create_iff (trans_fmla f1 id_typ_map) (trans_fmla f2 id_typ_map)
  | F_forall (id, typ_opt, f) -> 
    (
      match typ_opt with
      | Some T_int -> 
        Fmla.create_forall (Expr.create_var (Expr.sort_of_int()) ~name: id) (trans_fmla f id_typ_map)
      | Some T_bool ->
        Fmla.create_forall (Expr.create_var (Expr.sort_of_bool()) ~name: id) (trans_fmla f id_typ_map)
      | Some T_arr T_int ->
        Fmla.create_forall (Expr.create_var (Expr.sort_of_arr(Expr.sort_of_int())) ~name: id) (trans_fmla f id_typ_map)
      | Some T_arr T_bool ->
        Fmla.create_forall (Expr.create_var (Expr.sort_of_arr(Expr.sort_of_bool())) ~name: id) (trans_fmla f id_typ_map)
      | None -> 
        Fmla.create_forall (Expr.create_var (Expr.sort_of_int()) ~name: id) (trans_fmla f id_typ_map)
      | _ -> 
        raise (Failure "type does not match with typ")
    )
  | F_exists (id, typ_opt, f) ->
    (
      match typ_opt with
      | Some T_int -> 
        Fmla.create_exists (Expr.create_var (Expr.sort_of_int()) ~name: id) (trans_fmla f id_typ_map)
      | Some T_bool ->
        Fmla.create_exists (Expr.create_var (Expr.sort_of_bool()) ~name: id) (trans_fmla f id_typ_map)
      | Some T_arr T_int ->
        Fmla.create_exists (Expr.create_var (Expr.sort_of_arr(Expr.sort_of_int())) ~name: id) (trans_fmla f id_typ_map)
      | Some T_arr T_bool ->
        Fmla.create_exists (Expr.create_var (Expr.sort_of_arr(Expr.sort_of_bool())) ~name: id) (trans_fmla f id_typ_map)
      | None -> 
        Fmla.create_exists (Expr.create_var (Expr.sort_of_int()) ~name: id) (trans_fmla f id_typ_map)
      | _ -> 
        raise (Failure "type does not match with typ")
    )
  | F_sorted (id, e1, e2) -> 
    (* 
      start(e1) ~ end(e2) 까지 sort돼있는지   
      id[e1] <= id[e1+1] <= id[e1+2] <= id[e1+3] <= ... <= id[e2]
    *)
    (*
      ∀i,j (e1≤i≤j≤e2-1) -> (a[i]≤a[j])
    *)
    let new_fresh_var1 = generate_fresh_var() in
    let new_fresh_var2 = generate_fresh_var() in
    let left_cond = F_and [F_exp (E_le (e1, E_lv (V_var new_fresh_var1))); 
      F_exp (E_le (E_lv (V_var new_fresh_var1), E_lv (V_var new_fresh_var2))); 
      F_exp (E_le (E_lv (V_var new_fresh_var2), e2))] in
    let right_cond = F_exp (E_le (E_lv (V_arr (id, E_lv (V_var new_fresh_var1))), E_lv (V_arr (id, E_lv (V_var new_fresh_var2))))) in
    let left2right = F_imply (left_cond, right_cond) in
    let forall = F_forall (new_fresh_var1, Some T_int, F_forall (new_fresh_var2, Some T_int, left2right)) in
      trans_fmla forall id_typ_map
  | F_partitioned (id, e1, e2, e3, e4) -> 
    (*
      e1 ~ e2 사이의 모든 원소보다 e3 ~ e4 사이의 모든 원소가 더 큼
    *)
    (*
      ∀i,j (e1≤i≤e2<e3≤j≤e4)→(a[i]≤a[j])   
    *)
    let new_fresh_var1 = generate_fresh_var() in
    let new_fresh_var2 = generate_fresh_var() in
    let i_range_cond = F_and [F_exp (E_le (e1, E_lv (V_var new_fresh_var1))); F_exp (E_le (E_lv (V_var new_fresh_var1), e2)); F_exp (E_lt (e2, e3))] in
    let j_range_cond = F_and [F_exp (E_le (e3, E_lv (V_var new_fresh_var2))); F_exp (E_le (E_lv (V_var new_fresh_var2), e4))] in
    let range_cond = F_and [i_range_cond; j_range_cond] in
    let partition_cond = F_exp (E_le (E_lv (V_arr (id, E_lv (V_var new_fresh_var1))), E_lv (V_arr (id, E_lv (V_var new_fresh_var2))))) in
    let left2right = F_imply (range_cond, partition_cond) in
    let forall = F_forall (new_fresh_var1, Some T_int, F_forall (new_fresh_var2, Some T_int, left2right)) in
      trans_fmla forall id_typ_map
  

let rec make_id_typ_map : decl list -> (id, typ) BatMap.t -> (id, typ) BatMap.t
=fun args_locals id_typ_map ->
  match args_locals with
  | (typ, id)::tl ->
    let new_id_typ_map = BatMap.add id typ id_typ_map in
      make_id_typ_map tl new_id_typ_map
  | [] -> id_typ_map


let rec dfs_node_lst : Graph.Node.t -> Graph.Cfg.t -> Graph.Node.t list -> Graph.Node.t list list
=fun start_node cfg before_lst ->
  let next_node_set = Graph.Cfg.succs start_node cfg in
  let ref_lst : Graph.Node.t list list ref = ref [] in
  let _ = 
    Graph.NodeSet.iter ( fun node ->
      let new_node = 
        (
          match Graph.Node.get_instr node with
          | I_return e -> 
            Graph.Node.create_assign (V_var "rv") e
          | _ -> node
        ) in
      let is_call = match Graph.Node.get_instr node with | I_call _ -> true | _ -> false in
      if is_call = true then 
        let _ = (ref_lst := !ref_lst@[before_lst@[new_node]]) in
        let lst = dfs_node_lst node cfg (before_lst@[new_node]) in (ref_lst := !ref_lst@lst)
      else
        if check_end_of_lst node = true then (ref_lst := !ref_lst@[before_lst@[new_node]])
        else 
          let lst = dfs_node_lst node cfg (before_lst@[new_node]) in (ref_lst := !ref_lst@lst)
    ) next_node_set in 
    !ref_lst
and check_end_of_lst : Graph.Node.t -> bool
=fun node -> 
  match Graph.Node.get_instr node with
  | I_loop_entry -> true
  | I_function_exit -> true
  | _ -> false 

let make_bp_lst : Graph.Cfg.t -> Graph.Node.t list list
=fun cfg ->
  let node_lst = Graph.Cfg.nodesof cfg in
  let rec iter_node_lst : Graph.Node.t list -> Graph.Node.t list list -> Graph.Node.t list list
  =fun node_lst ret_lst ->
    match node_lst with
    | node::tl ->
      (
        match Graph.Node.get_instr node with
        | I_function_entry | I_loop_entry -> 
          iter_node_lst tl (ret_lst@(dfs_node_lst node cfg [node]))
        | _ -> iter_node_lst tl ret_lst
      )
    | [] -> ret_lst in
  let lst = iter_node_lst node_lst [] in lst

let wp_id = ref 0
let new_replace_inv decl e inv =
  let (_, x) = decl in 
  let (_, f) = inv in
  wp_id := !wp_id + 1;
  ("WP" ^ string_of_int !wp_id, Syntax.replace_fmla x e f)

let wp_sub : fmla -> Graph.Node.t -> Graph.Cfg.t -> bool -> fmla
=fun post c cfg total ->
  match Graph.Node.get_instr c with
  | I_call (id, _, actuals) ->
    let replace_call inv decl_lst el =
      list_fold (fun (decl, e) inv ->
        new_replace_inv decl e inv
      ) (zip decl_lst el) inv in
      let (_, pre) = new_replace_inv (T_bool, id) (E_lv (V_var "res")) ("", post) in
      let (_, new_pre) = replace_call ("", pre) (Graph.Cfg.get_args cfg) actuals in 
      if total = true then 
        new_pre
      else 
        F_imply (new_pre, post)
  | I_assume e -> 
    F_imply (F_exp e, post)
  | I_assign (V_var id, e) ->
    let (_, new_fmla) = new_replace_inv (T_int, id) e ("", post) in new_fmla
  | I_assign ((V_arr (id, e1)), e2) ->
    let a = E_arr_update (id, e1, e2) in
    let eq = E_eq (a, E_lv (V_var id)) in F_imply (F_exp eq, post)
  | _ -> post

let rec weak_precond_sub : Graph.Node.t list -> Graph.Cfg.t -> fmla -> bool -> fmla
=fun bp cfg post_cond_fmla total ->
  match bp with
  | node::tl -> 
    let new_fmla = wp_sub post_cond_fmla node cfg total in
    weak_precond_sub tl cfg new_fmla total
  | [] -> post_cond_fmla

let rec weak_precond : Graph.Cfg.t -> Graph.Node.t list list -> bool -> fmla list
=fun cfg bp_lst total ->
  match bp_lst with
  | bp::tl -> 
    let (_, pre_cond_fmla) = match Graph.Cfg.get_invariant (get_hd bp) cfg with | Some inv -> inv | None -> raise (Failure "Last Node is not invariant") in
    let bp = reverse_lst bp in
    let (_, post_cond_fmla) = match Graph.Cfg.get_invariant (get_hd bp) cfg with | Some inv -> inv | None -> raise (Failure "Last Node is not invariant") in
    let bp = get_tl bp in
      [F_imply (pre_cond_fmla, weak_precond_sub bp cfg post_cond_fmla total)]@(weak_precond cfg tl total)
  | [] -> []


let rec remove_true : fmla list -> fmla list
=fun fmla_lst ->
  match fmla_lst with
  | fmla::tl ->
    (remove_true_sub fmla)::(remove_true tl)
  | [] -> []
and remove_true_sub : fmla -> fmla
=fun f ->
  match f with
  | F_exp _ | F_order _ | F_sorted _ | F_partitioned _ -> f
  | F_not f -> remove_true_sub f
  | F_and fs -> let new_f = (List.map (fun x -> remove_true_sub x) fs) in F_and new_f
  | F_or fs -> let new_f = (List.map (fun x -> remove_true_sub x) fs) in F_or new_f
  | F_imply (f1, f2) -> 
    F_imply (remove_true_sub f1, remove_true_sub f2)
  | F_iff (f1, f2) -> if f1 = F_exp (E_bool true) then f2 else f
  | F_forall (id, typ_opt, f') -> 
    let new_fresh_var = generate_fresh_var() in
    let fmla = replace_fmla id (E_lv (V_var new_fresh_var)) f' in
      F_forall (new_fresh_var, typ_opt, fmla)
  | F_exists (id, typ_opt, f') -> 
    let new_fresh_var = generate_fresh_var() in
    let fmla = replace_fmla id (E_lv (V_var new_fresh_var)) f' in
      F_exists (new_fresh_var, typ_opt, fmla)


let verify_partial_correctness : Syntax.pgm -> bool 
=fun pgm -> 
  let id_typ_map : (id, typ) BatMap.t = BatMap.empty in
  let args_locals = (pgm.args@pgm.locals) in
  let id_typ_map = make_id_typ_map args_locals id_typ_map in
  let id_typ_map = BatMap.add "rv" pgm.typ id_typ_map in
  let cfg = Graph.pgm2cfg pgm in 
  let bp_lst = make_bp_lst cfg in
  let fmla_lst = weak_precond cfg bp_lst false in
  let fmla_lst = remove_true fmla_lst in
  let bool_lst = 
    List.map ( fun fmla ->
      let transed_fmla = trans_fmla fmla id_typ_map in
      let v, _ = Solver.check_validity [transed_fmla] in Solver.is_valid v
    ) fmla_lst in
  let rec iter_bool_lst bool_lst = 
    match bool_lst with
    | hd::tl -> 
      if hd = false then hd else iter_bool_lst tl
    | [] -> true in
    iter_bool_lst bool_lst 



(***********************************************************************************************************)

let bigand f l = F_and (List.map f l)
let bigor f l = F_or (List.map f l)

let rec weak_precond_rank : Graph.Cfg.t -> rank -> fmla -> Graph.Node.t list list -> fmla list
=fun cfg rank rank_cond bp_lst ->
  match bp_lst with
  | bp::tl -> 
    let (_, pre_cond_fmla') = match Graph.Cfg.get_invariant (get_hd bp) cfg with | Some inv -> inv | None -> raise (Failure "Last Node is not invariant") in
    (* let pre_cond_fmla = bigand (fun i -> F_exp (E_le (E_int 0, (List.nth rank i)))) (range (List.length rank)) in *)
    let bp = get_tl (reverse_lst bp) in
    let new_rank_cond = weak_precond_sub bp cfg rank_cond true in
      (* [F_and [pre_cond_fmla'; new_rank_cond]]@(weak_precond_rank cfg rank new_rank_cond tl) *)
      [F_imply (pre_cond_fmla', new_rank_cond)]@(weak_precond_rank cfg rank new_rank_cond tl)
  | [] -> []

let rec compare_rank : exp list -> exp list -> fmla
=fun el1 el2 ->
  let el = process_lst el1 el2 in
  bigor ( fun i ->
    let e1, e2 = List.nth el i in
    F_and [
      F_exp (E_le (E_int 0, e1));
      F_exp (E_lt (e1, e2));
      bigand ( fun j ->
        let ej1, ej2 = List.nth el j in
        F_and [
          F_exp (E_eq (ej1, ej2));
        ]
      ) (range i)
    ]
  ) (range (List.length el)) 
and process_lst : exp list -> exp list -> (exp * exp) list
=fun el1 el2 ->
  match (el1, el2) with
  | e1::tl1, e2::tl2 ->
    (e1, change_to_rand_exp e2)::(process_lst tl1 tl2)
  | [], [] -> []
  | _ -> raise (Failure "Length does not match")
and change_to_rand_exp : exp -> exp 
=fun e ->
  let new_zero = "_0" in
  match e with
  | E_lv (V_var id) -> E_lv (V_var (id ^ new_zero))
  | E_add (e1, e2) -> E_add (change_to_rand_exp e1, change_to_rand_exp e2)
  | E_sub (e1, e2) -> E_sub (change_to_rand_exp e1, change_to_rand_exp e2)
  | E_mul (e1, e2) -> E_mul (change_to_rand_exp e1, change_to_rand_exp e2)
  | E_div (e1, e2) -> E_div (change_to_rand_exp e1, change_to_rand_exp e2)
  | E_neg e -> E_neg (change_to_rand_exp e)
  | E_not e -> E_not (change_to_rand_exp e)
  | E_eq (e1, e2) -> E_eq (change_to_rand_exp e1, change_to_rand_exp e2)
  | E_neq (e1, e2) -> E_neq (change_to_rand_exp e1, change_to_rand_exp e2)
  | E_lt (e1, e2) -> E_lt (change_to_rand_exp e1, change_to_rand_exp e2)
  | E_gt (e1, e2) -> E_gt (change_to_rand_exp e1, change_to_rand_exp e2)
  | E_le (e1, e2) -> E_le (change_to_rand_exp e1, change_to_rand_exp e2)
  | E_ge (e1, e2) -> E_ge (change_to_rand_exp e1, change_to_rand_exp e2)
  | _ -> e

let rec remove_rand_exp : exp -> exp 
=fun e -> 
  let re = Str.regexp "_0$" in
  match e with
  | E_lv (V_var id) -> E_lv (V_var (Str.replace_first re "" id))
  | E_add (e1, e2) -> E_add (remove_rand_exp e1, remove_rand_exp e2)
  | E_sub (e1, e2) -> E_sub (remove_rand_exp e1, remove_rand_exp e2)
  | E_mul (e1, e2) -> E_mul (remove_rand_exp e1, remove_rand_exp e2)
  | E_div (e1, e2) -> E_div (remove_rand_exp e1, remove_rand_exp e2)
  | E_neg e -> E_neg (remove_rand_exp e)
  | E_not e -> E_not (remove_rand_exp e)
  | E_eq (e1, e2) -> E_eq (remove_rand_exp e1, remove_rand_exp e2)
  | E_neq (e1, e2) -> E_neq (remove_rand_exp e1, remove_rand_exp e2)
  | E_lt (e1, e2) -> E_lt (remove_rand_exp e1, remove_rand_exp e2)
  | E_gt (e1, e2) -> E_gt (remove_rand_exp e1, remove_rand_exp e2)
  | E_le (e1, e2) -> E_le (remove_rand_exp e1, remove_rand_exp e2)
  | E_ge (e1, e2) -> E_ge (remove_rand_exp e1, remove_rand_exp e2)
  | _ -> e
and remove_rand_fmla : fmla -> fmla
=fun f ->
  match f with
  | F_exp e -> F_exp (remove_rand_exp e)
  | F_order _ -> f
  | F_not f -> F_not (remove_rand_fmla f)
  | F_and fs -> F_and (List.map remove_rand_fmla fs)
  | F_or fs -> F_or (List.map remove_rand_fmla fs)
  | F_imply (f1, f2) -> F_imply (remove_rand_fmla f1, remove_rand_fmla f2)
  | F_iff (f1, f2) -> F_iff (remove_rand_fmla f1, remove_rand_fmla f2)
  | F_forall (id, typ_opt, f') -> F_forall (id, typ_opt, remove_rand_fmla f')
  | F_exists (id, typ_opt, f') -> F_exists (id, typ_opt, remove_rand_fmla f')
  | F_sorted (id, e1, e2) -> F_sorted (id, remove_rand_exp e1, remove_rand_exp e2)
  | F_partitioned (id, e1, e2, e3, e4) -> F_partitioned (id, remove_rand_exp e1, remove_rand_exp e2, remove_rand_exp e3, remove_rand_exp e4)

let get_rank_pair : Graph.Node.t list -> Graph.Cfg.t -> (rank * rank)
=fun bp_lst cfg ->
  let hd_bp_lst = get_hd bp_lst in
  let tl_bp_lst = get_last_el bp_lst in
  (* let rank_hd = match Graph.Cfg.get_rank hd_bp_lst cfg with | Some rank -> rank | None -> raise (Failure "No rank in node") in
  let rank_tl = match Graph.Cfg.get_rank tl_bp_lst cfg with | Some rank -> rank | None -> raise (Failure "No rank in node") in
    (rank_hd, rank_tl) *)
  let rank_hd = match Graph.Cfg.get_rank hd_bp_lst cfg with | Some rank -> rank | None -> raise (Failure "No rank in node") in
  match Graph.Cfg.get_rank tl_bp_lst cfg with | Some rank -> (rank_hd, rank) | None -> (rank_hd, rank_hd)

let rec extract_bp_lst : Graph.Node.t list list -> Graph.Node.t list list 
=fun bp_lst ->
  match bp_lst with
  | bp::tl ->
    if is_loop_entry bp = true then bp::(extract_bp_lst tl)
    else 
      (* if is_recursive bp = true then (remove_call bp)::(extract_bp_lst tl) *)
        if is_recursive bp = true then (bp)::(extract_bp_lst tl)
      else extract_bp_lst tl
  | [] -> []
and is_loop_entry : Graph.Node.t list -> bool
=fun bp ->
  let hd_of_bp = get_hd bp in
  let tl_of_bp = get_last_el bp in
  let hd_instr = Graph.Node.get_instr hd_of_bp in
  let tl_instr = Graph.Node.get_instr tl_of_bp in
  if hd_instr = Graph.Node.I_loop_entry && tl_instr = Graph.Node.I_loop_entry then true
  else false
and is_recursive: Graph.Node.t list -> bool
=fun bp ->
  let hd_of_bp = get_hd bp in
  let tl_of_bp = get_last_el bp in
  let hd_instr = Graph.Node.get_instr hd_of_bp in
  let tl_instr = Graph.Node.get_instr tl_of_bp in
  let rec iter_bp : Graph.Node.t list -> bool
  =fun bp ->
    match bp with
    | node::tl ->
      let instr = Graph.Node.get_instr node in
      (
        match instr with
        | I_call _ -> true
        | _ -> iter_bp tl
      )
    | [] -> false in
  if hd_instr = Graph.Node.I_function_entry && 
    tl_instr = Graph.Node.I_function_exit && 
    iter_bp bp = true
  then true
  else false
and remove_call : Graph.Node.t list -> Graph.Node.t list
=fun bp ->
  match bp with
  | node::tl ->
    let instr = Graph.Node.get_instr node in
    (
      match instr with
      | I_call _ -> remove_call tl
      | I_assign (V_var id, _) -> 
        if id <> "rv" then (node)::(remove_call tl) else remove_call tl
      | _ -> (node)::(remove_call tl)
    )
  | [] -> []

let verify_termination : Syntax.pgm -> bool 
=fun pgm ->   
  let id_typ_map : (id, typ) BatMap.t = BatMap.empty in
  let args_locals = (pgm.args@pgm.locals) in
  let id_typ_map = make_id_typ_map args_locals id_typ_map in ignore id_typ_map;
  let id_typ_map = BatMap.add "rv" pgm.typ id_typ_map in
  let cfg = Graph.pgm2cfg pgm in 
  let bp_lst = make_bp_lst cfg in
  let loop_bp_lst = extract_bp_lst bp_lst in
  let bool_lst = List.map ( fun bp ->
    let rank1, rank2 = get_rank_pair bp cfg in
    let rank_cond = compare_rank rank2 rank1 in
    let wp = weak_precond_rank cfg rank1 rank_cond [bp] in
    let hd_wp = get_hd wp in
    let hd_wp = remove_rand_fmla hd_wp in
    let transed_fmla = trans_fmla hd_wp id_typ_map in
    let v, _ = Solver.check_validity [transed_fmla] in Solver.is_valid v
  ) loop_bp_lst in
  let rec iter_bool_lst bool_lst = 
    match bool_lst with
    | hd::tl -> 
      if hd = false then false else iter_bool_lst tl
    | [] -> true in
    iter_bool_lst bool_lst


