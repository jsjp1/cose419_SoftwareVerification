type abs = 
| INF
| NUM of int
| BOT
type matrix = abs array array


let print_abs abs = 
  match abs with
  | INF -> print_string "INF "
  | NUM n -> print_int n; print_string " "
  | BOT -> print_string "BOT "

let print_var_lst vl = 
  (print_string "Variables: \n");
  (List.iter (fun x -> print_string (x ^ " ")) vl);
  (print_string "\n\n")

let print_node node = (print_string (Cfg.Node.to_string node ^ " "))

let print_node_lst nl = 
  (print_string "Nodes: \n");
  (List.iter (fun node -> print_node node) nl);
  (print_string "\n\n")

let print_matrix mat =
  let n = Array.length mat in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      match mat.(i).(j) with
      | INF -> print_string "INF "
      | NUM n -> print_int n; print_string "   "
      | BOT -> print_string "BOT "
    done;
    print_string "\n"
  done

let print_matrix_lst mat_lst =
  List.iter (fun mat -> print_matrix mat) mat_lst

let rec reverse_lst lst =
  match lst with
  | hd::tl -> (reverse_lst tl)@[hd]
  | [] -> []

let rec remove_skip wl cfg =
  match wl with
  | node::tl ->
    (
      match Cfg.Node.get_instr node with
      | I_skip -> 
        if Cfg.Cfg.is_loophead node cfg then node::(remove_skip tl cfg)
        else remove_skip tl cfg
      | _ -> node::(remove_skip tl cfg)
    )
  | [] -> []

let make_var_int_map vl = 
  let map = ref BatMap.empty in
  let _ = List.iteri (fun i x -> map := BatMap.add x (i+1) !map) vl in
  !map

let make_worklist cfg = 
  let worklist = ref [] in
  let _ = List.iter ( fun n -> 
    worklist := !worklist@[n]
  ) cfg in
  !worklist

let find_preds node cfg =
  (* node의 직접적인 선행 노드들을 가져옴 *)
  let direct_preds = Cfg.Cfg.preds node cfg in
  Cfg.NodeSet.fold (fun pred acc ->
    Cfg.NodeSet.add pred acc
  ) direct_preds Cfg.NodeSet.empty

let print_input_of_node cfg =
  let node_lst = Cfg.Cfg.nodesof cfg in
  List.iter (fun node ->
    let _ = print_string ("Node: " ^ Cfg.Node.to_string node ^ "\n") in
    let preds = find_preds node cfg in
    Cfg.NodeSet.iter (fun pred ->
      print_string ("Parents: " ^ Cfg.Node.to_string pred ^ "\n")
    ) preds;
    print_string "\n";
  ) node_lst

let get_input_of_node node cfg =
  (* 주어진 node의 input node 반환 *)
  let ref_lst = ref [] in
  let _ = List.iter (fun node ->
    let preds = find_preds node cfg in
    Cfg.NodeSet.iter (fun pred ->
      ref_lst := pred::!ref_lst
    ) preds;
  ) [node] in ref_lst

let rec init_matrix_map : (Cfg.Node.t, matrix) BatMap.t ref -> Cfg.Node.t list -> int -> unit
=fun map node_lst len ->
  (* 모든 Node의 bot matrix 생성 *)
  match node_lst with
  | node::tl ->
    let new_mat = Array.make_matrix (len+1) (len+1) BOT in
    (map := BatMap.add node new_mat !map);
      init_matrix_map map tl len
  | [] -> ()

let get_input_matrix_lst : (Cfg.Node.t, matrix) BatMap.t ref -> Cfg.Node.t list -> matrix list
=fun map input_lst->
  (* input_lst의 matrix 반환 *)
  List.map (fun n -> BatMap.find n !map) input_lst

let clear_diag : matrix -> matrix
=fun mat ->
  (* 대각선을 0으로 변환 *)
  let n = Array.length mat in
  for i = 0 to n - 1 do
    mat.(i).(i) <- NUM 0
  done;
  mat

let fresh_matrix : int -> matrix 
=fun len -> 
  (* 대각선은 0이고, 나머지는 INF인 array 생성 *)
  let mat = Array.make_matrix (len+1) (len+1) INF in
  clear_diag mat

let remove_info : matrix -> Syntax.var -> (Syntax.var, int) BatMap.t -> unit
=fun mat var var_int_map ->
  (* matrix의 var에 해당하는 라인의 값을 INF로 변경 후 반환 *)
  let len = Array.length mat in
  let idx = BatMap.find var var_int_map in
  for i = 0 to len - 1 do
    mat.(i).(idx) <- INF; mat.(idx).(i) <- INF
  done

let normalize : matrix -> matrix
=fun mat ->
  let n = Array.length mat in
  for k = 0 to n - 1 do
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        (
          match mat.(i).(k), mat.(k).(j), mat.(i).(j) with
          | INF, _, _ -> ()
          | _, INF, _ -> ()
          | NUM a, NUM b, INF -> mat.(i).(j) <- NUM (a + b)
          | NUM a, NUM b, NUM c -> if a + b < c then mat.(i).(j) <- NUM (a + b)
          | _ -> ()
        )
      done;
    done;
  done;
  clear_diag mat

let get_element_matrix : matrix -> int -> int -> abs
=fun mat i j -> mat.(i).(j)

let change_element_matrix : matrix -> int -> int -> abs -> unit
=fun mat i j abs ->
  (mat.(i).(j) <- abs)

let change_row_matrix : matrix -> int -> abs -> unit
=fun mat row abs -> 
  for col = 0 to (Array.length mat) - 1 do
    let n = get_element_matrix mat row col in
    match n with
    | INF -> ()
    | NUM n -> 
      (
        match abs with
        | NUM i -> mat.(row).(col) <- (NUM (n + i))
        | _ -> mat.(row).(col) <- abs
      )
    | BOT -> mat.(row).(col) <- abs
  done

let change_col_matrix : matrix -> int -> abs -> unit
=fun mat col abs -> 
  for row = 0 to (Array.length mat) - 1 do
    let n = get_element_matrix mat row col in
    match n with
    | INF -> ()
    | NUM n -> 
      (
        match abs with
        | NUM i -> mat.(row).(col) <- (NUM (n + i))
        | _ -> mat.(row).(col) <- abs
      )
    | BOT -> mat.(row).(col) <- abs
  done

let rec is_aexp_include_var : Syntax.aexp -> Syntax.var -> bool
=fun ae var ->
  match ae with
  | Const _ -> false
  | Var id -> if id = var then true else false
  | Add (ae1, ae2) -> (is_aexp_include_var ae1 var) || (is_aexp_include_var ae2 var)
  | Sub (ae1, ae2) -> (is_aexp_include_var ae1 var) || (is_aexp_include_var ae2 var)
  | Mult (ae1, ae2) -> (is_aexp_include_var ae1 var) || (is_aexp_include_var ae2 var)
and check_all_bot : matrix -> bool
=fun mat ->
  let n = Array.length mat in
  let res = ref true in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if mat.(i).(j) <> BOT then res := false
    done;
  done;
  !res

let join_matrix_element_wise : matrix list -> matrix
=fun ml ->
  (* matrix list를 element wise join *)
  if (List.length ml = 1) then
    if (check_all_bot (List.hd ml)) then
      fresh_matrix (Array.length (List.hd ml) - 1)
    else List.hd ml 
  else
    let n = Array.length (List.hd ml) in
    let m1 = List.hd ml in
    let m2 = List.hd (List.tl ml) in
    let mat = Array.make_matrix n n BOT in
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        (
          match m1.(i).(j), m2.(i).(j) with
          | BOT, NUM n | NUM n, BOT -> mat.(i).(j) <- NUM n
          | INF, _ | _, INF -> mat.(i).(j) <- INF 
          | NUM n1, NUM n2 ->
            if n1 < n2 then 
              mat.(i).(j) <- NUM n2
            else 
              mat.(i).(j) <- NUM n1
          | _, _ -> mat.(i).(j) <- m1.(i).(j)
        )
      done;
    done; mat

let rec process_aexp : Syntax.aexp -> matrix -> (string, int) BatMap.t -> abs
=fun ae mat var_int_map -> 
  match ae with
  | Const n -> NUM n
  | Var id -> 
    let var_num = BatMap.find id var_int_map in
      get_element_matrix mat 0 var_num (* 0 var_num ? var_num 0 ? *) (* row == 0, column == var_num *)
  | Add (ae1, ae2) ->
    let processed_abs1 = process_aexp ae1 mat var_int_map in
    let processed_abs2 = process_aexp ae2 mat var_int_map in
    (
      match processed_abs1, processed_abs2 with
      | NUM n1, NUM n2 -> NUM (n1 + n2)
      | _, INF | INF, _ -> INF
      | BOT, _ -> processed_abs2
      | _, BOT -> processed_abs1
    )
  | Sub (ae1, ae2) ->
    let processed_abs1 = process_aexp ae1 mat var_int_map in
    let processed_abs2 = process_aexp ae2 mat var_int_map in
    (
      match processed_abs1, processed_abs2 with
      | NUM n1, NUM n2 -> NUM (n1 - n2)
      | _, INF | INF, _ -> INF
      | BOT, _ -> processed_abs2
      | _, BOT -> processed_abs1
    )
  | Mult (ae1, ae2) -> 
    let processed_abs1 = process_aexp ae1 mat var_int_map in
    let processed_abs2 = process_aexp ae2 mat var_int_map in
    (
      match processed_abs1, processed_abs2 with
      | NUM n1, NUM n2 -> NUM (n1 * n2)
      | _, INF | INF, _ -> INF
      | BOT, _ -> processed_abs2
      | _, BOT -> processed_abs1
    )


let rec extract_var : Syntax.aexp -> Syntax.var list -> Syntax.var list
=fun ae lst -> 
  match ae with
  | Const _ -> []
  | Var id -> lst@[id]
  | Add (ae1, ae2) -> (extract_var ae1 lst)@(extract_var ae2 lst)
  | Sub (ae1, ae2) -> (extract_var ae1 lst)@(extract_var ae2 lst)
  | Mult (ae1, ae2) -> (extract_var ae1 lst)@(extract_var ae2 lst)

let rec process_bexp : Syntax.bexp -> matrix -> (string, int) BatMap.t -> bool -> unit
=fun be mat var_int_map is_not -> 
  match be with
  | True -> ()
  | False -> ()
  | Equal (Var var1, Var var2) ->
    let var1_num = BatMap.find var1 var_int_map in
    let var2_num = BatMap.find var2 var_int_map in
    let processed_abs1 = process_aexp (Var var1) mat var_int_map in
    let processed_abs2 = process_aexp (Var var2) mat var_int_map in
    (
      match processed_abs1, processed_abs2 with
      | NUM n, NUM m ->
        if n <= m then
          let _ = change_element_matrix mat 0 var1_num (NUM m) in
            change_element_matrix mat var1_num 0 (NUM (-m))
        else 
          let _ = change_element_matrix mat 0 var2_num (NUM n) in
            change_element_matrix mat var2_num 0 (NUM (-n))
      | _ -> ()
    )
  | Equal (Var var, ae2) -> (* ae1과 ae2가 같다는 전제하에 path를 만듦 *)
    let var_num = BatMap.find var var_int_map in
    let processed_abs1 = process_aexp (Var var) mat var_int_map in
    let processed_abs2 = process_aexp ae2 mat var_int_map in
    (
      match processed_abs1, processed_abs2 with
      | NUM n, NUM m ->
        if n <= m then
          let _ = change_element_matrix mat 0 var_num (NUM n) in
            change_element_matrix mat var_num 0 (NUM (-n))
        else ()
      | _, INF -> 
        let var_num = BatMap.find var var_int_map in
        let _ = change_element_matrix mat var_num 0 INF in
          change_element_matrix mat 0 var_num INF
      | _, BOT -> 
        let var_num = BatMap.find var var_int_map in
        let _ = change_element_matrix mat var_num 0 BOT in
          change_element_matrix mat 0 var_num BOT
      | _ -> ()
    )
  | Equal (ae1, Var var) -> (* ae1과 ae2가 같다는 전제하에 path를 만듦 *)
    let processed_abs1 = process_aexp ae1 mat var_int_map in
    let processed_abs2 = process_aexp (Var var) mat var_int_map in
    (
      match processed_abs1, processed_abs2 with
      | NUM n, _ -> 
        let var_num = BatMap.find var var_int_map in
        let _ = change_element_matrix mat var_num 0 (NUM (-n)) in
          change_element_matrix mat 0 var_num (NUM n)
      | INF, _ -> 
        let var_num = BatMap.find var var_int_map in
        let _ = change_element_matrix mat var_num 0 INF in
          change_element_matrix mat 0 var_num INF
      | BOT, _ -> 
        let var_num = BatMap.find var var_int_map in
        let _ = change_element_matrix mat var_num 0 BOT in
          change_element_matrix mat 0 var_num BOT
    )
  | Le (Var var, ae2) -> 
    (* is_not == true -> Le (x, 9) == x > 9 *)
    let var_num = BatMap.find var var_int_map in
    if is_not then (* x > 9 *)
      let processed_abs1 = get_element_matrix mat var_num 0 in
      let processed_abs2 = process_aexp ae2 mat var_int_map in
      (
        match processed_abs1, processed_abs2 with
        | NUM n, NUM m -> 
          if n <= m then 
            change_element_matrix mat var_num 0 (NUM (-(m+1)))
          else ()
        | INF, NUM m -> 
          change_element_matrix mat var_num 0 (NUM (-(m+1)))
        | _, _ -> ()
      )
    else 
      let processed_abs1 = process_aexp (Var var) mat var_int_map in
      let processed_abs2 = process_aexp ae2 mat var_int_map in
      (
        match processed_abs1, processed_abs2 with
        | NUM n, NUM m -> 
          if n <= m then
            change_element_matrix mat 0 var_num (NUM n)
          else 
            change_element_matrix mat 0 var_num (NUM m)
        | INF, _ ->
          change_element_matrix mat 0 var_num processed_abs2
        | _, _ -> ()
      )
  | Le (ae1, Var var) -> (* 0 <= x *)
    let var_num = BatMap.find var var_int_map in
    if is_not then
      let processed_abs1 = process_aexp ae1 mat var_int_map in
      let processed_abs2 = process_aexp (Var var) mat var_int_map in
      (
        match processed_abs1, processed_abs2 with
        | NUM n, NUM m -> 
          if m < n then 
            change_element_matrix mat 0 var_num (NUM n)
          else ()
        | NUM _, INF -> ()
        | _, _ -> ()
      )
    else 
      let processed_abs1 = process_aexp ae1 mat var_int_map in
      let processed_abs2 = process_aexp (Var var) mat var_int_map in
      (
        match processed_abs1, processed_abs2 with
        | NUM n, NUM m -> 
          if m < n then
            change_element_matrix mat 0 var_num (NUM n)
          else ()
        | INF, _ ->
          change_element_matrix mat 0 var_num processed_abs2
        | _, _ -> ()
      )
  | Not be ->
    process_bexp be mat var_int_map true
  | _ -> ()


let check_mat_diff : matrix -> matrix -> bool
=fun mat1 mat2 ->
  let n = Array.length mat1 in
  let m = Array.length mat1.(0) in
  let res = ref false in
  for i = 0 to n - 1 do
    for j = 0 to m - 1 do
      if mat1.(i).(j) <> mat2.(i).(j) then res := true
    done;
  done;
  !res

let widening : matrix -> matrix -> unit
(* origin output matrix, new output matrix -> 증가한것들을 INF로 변경한 matrix 반환 *)
=fun origin_mat new_mat ->
  let n = Array.length origin_mat in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      match origin_mat.(i).(j), new_mat.(i).(j) with
      | NUM n1, NUM n2 -> 
        if n1 < n2 then new_mat.(i).(j) <- INF else new_mat.(i).(j) <- NUM n2
      | _, INF | INF, _ -> new_mat.(i).(j) <- INF
      | BOT, NUM n | NUM n, BOT -> new_mat.(i).(j) <- NUM n
      | _ -> new_mat.(i).(j) <- new_mat.(i).(j)
    done;
  done

let narrowing : matrix -> matrix -> unit
(* origin output matrix, new output matrix -> 감소한것들을 감소한 숫자로 변경한 matrix 반환 *)
=fun origin_mat new_mat ->
  let n = Array.length origin_mat in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      match origin_mat.(i).(j), new_mat.(i).(j) with
      | NUM n1, NUM n2 -> 
        if n1 > n2 then new_mat.(i).(j) <- NUM n2 else new_mat.(i).(j) <- NUM n1
      | _, NUM n -> new_mat.(i).(j) <- NUM n
      | _, BOT -> new_mat.(i).(j) <- BOT
      | _ -> ()
    done;
  done

let copy_map : matrix -> matrix
=fun mat ->
  let n = Array.length mat in
  let copied_mat = Array.make_matrix n n BOT in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      copied_mat.(i).(j) <- mat.(i).(j)
    done;
  done;
  copied_mat

let rec extract_none_var : Syntax.aexp -> Syntax.var -> Syntax.aexp
=fun ae var ->
  match ae with
  | Const n -> Const n
  | Var id -> if id = var then Const 0 else Var id
  | Add (ae1, ae2) -> Add (extract_none_var ae1 var, extract_none_var ae2 var)
  | Sub (ae1, ae2) -> Sub (extract_none_var ae1 var, extract_none_var ae2 var)
  | Mult (ae1, ae2) -> Mult (extract_none_var ae1 var, extract_none_var ae2 var)

(* TODO: skip을 다삭제하지는말고, loop entry, ... 등의 것들만 남겨두고 삭제. *)
let rec iter_work_lst : bool -> bool -> Cfg.Cfg.t -> (Cfg.Node.t, matrix) BatMap.t ref -> Cfg.Node.t list -> (string, int) BatMap.t -> int -> unit
=fun fixed is_widening cfg matrix_map work_lst var_int_map len ->
  match work_lst with
  | node::tl -> 
    (
      match Cfg.Node.get_instr node with
      | I_assign (var, ae) -> 
        let input_node_lst = get_input_of_node node cfg in
        let input_mat_lst = get_input_matrix_lst matrix_map !input_node_lst in
        let init_matrix = 
          if (List.length input_mat_lst) = 0
          then fresh_matrix len 
          else join_matrix_element_wise input_mat_lst in

        let aexp_include_var = is_aexp_include_var ae var in
        let _ = 
          if aexp_include_var then ()
          else remove_info init_matrix var var_int_map  in
        let processed_abs = process_aexp ae init_matrix var_int_map in
        let var_num = BatMap.find var var_int_map in

        let new_mat = copy_map init_matrix in

        let _ = 
          if aexp_include_var then 
            let extract_var = extract_none_var ae var in
            let processed_abs = process_aexp extract_var init_matrix var_int_map in
            let _ = change_row_matrix new_mat var_num (match processed_abs with | NUM n -> NUM (-n) | _ -> INF) in
              change_col_matrix new_mat var_num (match processed_abs with | NUM n -> NUM n | _ -> INF)
          else
            let _ = change_element_matrix new_mat 0 var_num (match processed_abs with | NUM n -> NUM n | _ -> INF) in
              change_element_matrix new_mat var_num 0 (match processed_abs with | NUM n -> NUM (-n) | _ -> INF) in

        let _ = normalize new_mat in
        (matrix_map := BatMap.add node new_mat !matrix_map);

        if aexp_include_var then
          if fixed then 
            iter_work_lst fixed is_widening cfg matrix_map tl var_int_map len
          else 
            iter_work_lst fixed is_widening cfg matrix_map (tl@[node]) var_int_map len
        else 
          iter_work_lst fixed is_widening cfg matrix_map tl var_int_map len
      | I_assume be -> 
        let input_node_lst = get_input_of_node node cfg in
        let input_mat_lst = get_input_matrix_lst matrix_map !input_node_lst in
        let init_matrix = if (List.length input_mat_lst = 0) 
          then fresh_matrix len 
          else join_matrix_element_wise input_mat_lst in
        
        let new_mat = copy_map init_matrix in
        let _ = process_bexp be new_mat var_int_map false in
        let _ = normalize new_mat in

        (matrix_map := BatMap.add node new_mat !matrix_map);

          if fixed then
            iter_work_lst fixed is_widening cfg matrix_map tl var_int_map len
          else
            iter_work_lst fixed is_widening cfg matrix_map (tl@[node]) var_int_map len
      | I_assert be -> 
        if fixed = false then 
          iter_work_lst fixed is_widening cfg matrix_map (tl@[node]) var_int_map len
        else
          let input_node_lst = get_input_of_node node cfg in
          let input_mat_lst = get_input_matrix_lst matrix_map !input_node_lst in
          let init_matrix = if (List.length input_mat_lst = 0) 
            then fresh_matrix len 
            else join_matrix_element_wise input_mat_lst in
          let new_mat = copy_map init_matrix in
          let _ = process_bexp be new_mat var_int_map false in

          let _ = normalize new_mat in
            (matrix_map := BatMap.add node new_mat !matrix_map);
            iter_work_lst fixed is_widening cfg matrix_map tl var_int_map len
      | I_skip -> 
        (* TODO: fixed point만들기. 수행한결과가 이전과 같으면 work list에 포함 X *)
        let input_node_lst = get_input_of_node node cfg in
        let input_mat_lst = get_input_matrix_lst matrix_map !input_node_lst in
        let origin_output_mat = BatMap.find node !matrix_map in
        let init_matrix = if (List.length input_mat_lst = 0) 
          then fresh_matrix len 
          else join_matrix_element_wise input_mat_lst in

        let new_mat = copy_map init_matrix in
          if Cfg.Cfg.is_loophead node cfg then
            let _ = 
              if is_widening then 
                (widening origin_output_mat new_mat)
              else 
                (narrowing origin_output_mat new_mat)
              in
            (matrix_map := BatMap.add node new_mat !matrix_map);

            let is_changed = check_mat_diff origin_output_mat new_mat in
            if is_changed then
              iter_work_lst fixed is_widening cfg matrix_map (tl@[node]) var_int_map len
            else 
              let fixed = true in
              iter_work_lst fixed is_widening cfg matrix_map tl var_int_map len
          else 
            if (List.length input_mat_lst = 0) then
              let _ = matrix_map := BatMap.add node (fresh_matrix len) !matrix_map in
              if fixed then
                iter_work_lst fixed is_widening cfg matrix_map tl var_int_map len
              else 
                iter_work_lst fixed is_widening cfg matrix_map (tl@[node]) var_int_map len 
            else
              let _ = matrix_map := BatMap.add node (BatMap.find (List.hd !input_node_lst) !matrix_map) !matrix_map in
  
              if fixed then
                iter_work_lst fixed is_widening cfg matrix_map tl var_int_map len
              else iter_work_lst fixed is_widening cfg matrix_map (tl@[node]) var_int_map len
    )
  | [] -> ()

let rec skip_to_end : Cfg.Node.t list -> Cfg.Cfg.t -> Cfg.Node.t list
=fun lst cfg ->
  match lst with
  | node::tl -> 
    (
      match Cfg.Node.get_instr node with
      | I_skip -> 
        let input_node_lst = get_input_of_node node cfg in
        let _ = print_node_lst !input_node_lst in
          if (List.length !input_node_lst) = 0 then [node]@(skip_to_end tl cfg) (* 독립적인 skip이라면 *)
          else (skip_to_end tl cfg)@[node]
      | _ -> [node]@(skip_to_end tl cfg)
    )
  | [] -> []

let rec make_bp_lst : Cfg.Node.t -> Cfg.Node.t list ref -> Cfg.Cfg.t -> unit
=fun node lst cfg ->
  if check_exist node !lst then ()
  else (lst := !lst@[node]);
    let succs = Cfg.Cfg.succs node cfg in
    Cfg.NodeSet.iter( fun succ ->
      if check_exist succ !lst then ()
      else
        make_bp_lst succ lst cfg
    ) succs
and check_exist : Cfg.Node.t -> Cfg.Node.t list -> bool
=fun node lst ->
  match lst with
  | hd::tl ->
    if hd = node then true else check_exist node tl 
  | [] -> false


let rec check_assert : Syntax.bexp list -> matrix -> (string, int) BatMap.t -> int -> int
=fun be_lst mat var_int_map ret ->
  match be_lst with
  | be::tl ->
    let new_mat = copy_map mat in
    let bl = check_bexp be new_mat var_int_map in
    if bl then check_assert tl mat var_int_map (ret + 1) else check_assert tl mat var_int_map ret
  | [] -> ret
and check_bexp : Syntax.bexp -> matrix -> (string, int) BatMap.t -> bool
=fun be mat var_int_map -> 
  match be with
  | True -> true
  | False -> false
  | Equal (Var var1, Var var2) -> 
    let var1_num = BatMap.find var1 var_int_map in
    let var2_num = BatMap.find var2 var_int_map in
    let var1_value = get_element_matrix mat 0 var1_num in
    let var2_value = get_element_matrix mat 0 var2_num in
    (
      match var1_value, var2_value with
      | NUM n1, NUM n2 -> if n1 = n2 then true else false
      | _, _ -> false
    )
  | Equal (Var var, ae) | Equal (ae, Var var) -> 
    let processed_aexp1 = process_aexp (Var var) mat var_int_map in
    let processed_aexp2 = process_aexp ae mat var_int_map in
    (
      match processed_aexp1, processed_aexp2 with
      | NUM n1, NUM n2 -> if n1 = n2 then true else false
      | _, _ -> false
    )
  | Le (ae1, ae2) -> 
    let processed_aexp1 = process_aexp ae1 mat var_int_map in
    let processed_aexp2 = process_aexp ae2 mat var_int_map in
    (
      match processed_aexp1, processed_aexp2 with
      | NUM n1, NUM n2 -> if n1 <= n2 then true else false
      | _, INF | BOT, _ -> true
      | _, _ -> false
    )
  | Not be -> if check_bexp be mat var_int_map then false else true
  | _ -> false

let rec extract_assert_be_lst : Cfg.Node.t list -> Syntax.bexp list
=fun lst ->
  match lst with
  | hd::tl -> 
    (
      match Cfg.Node.get_instr hd with
      | I_assert be -> be::(extract_assert_be_lst tl)
      | _ -> extract_assert_be_lst tl
    )
  | [] -> []

let analyze : Syntax.pgm -> int 
=fun pgm ->
  let (vl, cmd) = pgm in
  let var_int_map = make_var_int_map vl in
  let cfg = Cfg.cmd2cfg cmd in
  let set = Cfg.Cfg.entries cfg in
  let entry = Cfg.NodeSet.choose set in
  let bp = ref [] in
  let _ = make_bp_lst entry bp cfg in

  let matrix_map : (Cfg.Node.t, matrix) BatMap.t ref = ref BatMap.empty  in
  let _ = init_matrix_map matrix_map !bp (List.length vl) in

  let is_fixed = false in
  let is_widening = true in
  let _ = iter_work_lst is_fixed is_widening cfg matrix_map !bp var_int_map (List.length vl) in
  let is_widening = false in (* narrowing *)
  let _ = iter_work_lst is_fixed is_widening cfg matrix_map !bp var_int_map (List.length vl) in
  let assert_be_lst = extract_assert_be_lst !bp in
  let res_cnt = check_assert assert_be_lst (BatMap.find (List.hd (List.rev !bp)) !matrix_map) var_int_map 0 in
    res_cnt