(* HES syntax and utils *)

open Util

type fp = Mu | Nu
type feq = Hflz.var * Hflz.ty * fp * Hflz.fml
type hes = feq list * Hflz.fml

let string_of_feq typ (v, ty, fp, fml) =
  if typ then
    sprintf "%s : %s =%s %s" (Hflz.string_of_var v) (Hflz.string_of_ty ty)
      (if fp = Mu then "μ " else "ν ") (Hflz.string_of_fml typ fml)
  else 
    sprintf "%s =%s %s" (Hflz.string_of_var v) 
      (if fp = Mu then "μ " else "ν ") (Hflz.string_of_fml typ fml)

let string_of_hes typ (feqs, f) = 
  sprintf "({\n%s},\n %s)"
    (List.fold_left (fun acc x -> sprintf "%s%s;\n" acc @@ string_of_feq typ x) "" feqs)
    (Hflz.string_of_fml typ f)

let to_hfl (hes : hes) =
  let feq_subst f x (v, ty, fp, fml) =
    if x = v then (v, ty, fp, fml) 
    else (v, ty, fp, Hflz.subst f x fml) in
  let rec aux = function
    | ([], f) -> f
    | ((v, ty, fp, fml)::xs, f) ->
      let f0 =
        match fp with
        | Mu -> Hflz.Mu (v, ty, fml)
        | Nu -> Hflz.Nu (v, ty, fml) in
      aux (List.map (feq_subst f0 v) xs, Hflz.subst f0 v f) in
  let ls, f = hes in
  aux (List.rev ls, f)

(* generate Map (func -> used funcs) from HES *)
let gen_used_funcs : hes -> S.t M.t = fun (feqs, f) ->
  let used_funcs_from_feq : feq -> Hflz.var * S.t = fun (v, _, _, fml) ->
    let s = Hflz.fv fml in
    v, s in
  let m = List.fold_left (fun map feq ->
      let v, s = used_funcs_from_feq feq in
      M.add v s map
    ) M.empty feqs in
  let main = ("main", "", -1) in
  M.(add main (Hflz.fv f) m)

(* calculate used funcs from given funcs and merge them *)
let add_used_funcs : S.t -> S.t M.t -> S.t = fun used m ->
  S.fold (fun elt s ->
      try
        let used_by_elt = M.find elt m in
        S.union s used_by_elt 
      with 
        Not_found -> s (* this is for free variables inside main *)
    ) used used

(* returns set of vars of used functions *)
let calc_used_funcs_from_main : hes -> S.t = fun hes ->
  let used_funcs = gen_used_funcs hes in
  let rec aux used =
    let used_ = add_used_funcs used used_funcs in
    if used <> used_ then
      aux used_ 
    else used in
  aux (S.singleton ("main", "", -1))

let remove_unused_feq : hes -> hes = fun (fs, f) ->
  let used_funcs = calc_used_funcs_from_main (fs, f) in
  let used_feqs = List.filter (fun (f,_,_,_) -> S.mem f used_funcs) fs in
  used_feqs, f

(* let gen_paramed_params : hes -> Hflz.var list M.t = fun (fs, f) ->
   let defined_funcs = List.map (fun (f,_,_,_) -> f) fs in
   let ord f1 f2 =
    let rec aux = function
      | [] -> []
      | f :: fs when f = f1 -> fs
      | f :: fs -> aux fs in
    if f1 = f2 then 0 
    else if List.mem f2 @@ aux defined_funcs then  -1 
    else 1 in
   let sort = List.sort ord in
   let used_funcs = gen_used_funcs (fs, f) in
   let gen_dep_funcs f before =
    let candidates = M.find f used_funcs in
    S.inter candidates before in
   let _, deps = List.fold_left (fun (before, res) f ->
      let dep_funcs = gen_dep_funcs f before in
      (S.add f before, M.add f dep_funcs res)
    ) (S.empty, M.empty) defined_funcs in
   let deep_deps deps = List.fold_left (fun res f ->
      let dep_funcs = M.find f deps in
      let deep_deps_funcs = S.fold (fun elt acc ->
          S.union (M.find elt res) acc
        ) dep_funcs dep_funcs in
      M.add f deep_deps_funcs res
    ) M.empty defined_funcs in
   (* let deep_deps = deep_deps deps in *)
   let rec saturate deps =
    let new_deps = deep_deps deps in
    if new_deps = deps then deps else saturate new_deps in
   M.map (fun s -> s |> S.elements |> sort) (saturate deps) *)

(* 引数としてとってこなければいけない関数は、
     (1) 依存していて、自分より上に定義されている関数
     (2) 依存している関数が依存している関数のうち、自分より上に定義されている関数
*)
(* 
generate a Map from a function name (f) to a set of function names
                    that the key function needs as parameters.
Such functions are
  (1) functions that appear in the body of f and are defined above f, or
  (2) functions that appear in functions that appear in the body of f 
      and are defined above f
*)
let gen_paramed_params : hes -> Hflz.var list M.t = fun (fs, f) ->
  let defined_funcs = List.map (fun (f,_,_,_) -> f) fs in
  let ord f1 f2 =
    let rec aux = function
      | [] -> []
      | f :: fs when f = f1 -> fs
      | f :: fs -> aux fs in
    if f1 = f2 then 0 
    else if List.mem f2 @@ aux defined_funcs then  -1 
    else 1 in
  let sort = List.sort ord in
  let used_funcs = gen_used_funcs (fs, f) in
  let gen_dep_funcs f before =
    let candidates = M.find f used_funcs in
    S.inter candidates before, candidates in
  let _, deps = List.fold_left (fun (before, res) f ->
      let dep_funcs = gen_dep_funcs f before in
      (S.add f before, M.add f dep_funcs res)
    ) (S.empty, M.empty) defined_funcs in
  let deep_deps deps =
    List.fold_left (fun (before, res) f ->
        (* let () = res
                 |> show_M (fun (x, y) -> Printf.sprintf "%s, %s" (show_S x) (show_S y)) 
                 |> print_endline in
           let () = Printf.printf "f : %s, before : %s\n" (Hflz.string_of_var f) (show_S before) in *)
        let dep_funcs, used_funcs = M.find f res in
        let deep_deps_funcs = S.fold (fun elt acc -> (* (1) *)
            try
              let fs, _ = M.find elt res in
              S.union fs acc
            with Not_found -> acc
          ) dep_funcs dep_funcs in
        let deep_deps_funcs =
          S.fold (fun elt acc -> (* (2) *)
              try
                let fs, _ = M.find elt res in
                (* let () = Printf.printf "%s -- %s\n" (Hflz.string_of_var elt) (show_S fs) in *)
                S.union fs acc
              with Not_found -> acc
            ) used_funcs deep_deps_funcs in
        (S.add f before, M.add f (S.inter before deep_deps_funcs, used_funcs) res)
      ) (S.empty, deps) defined_funcs in
  let rec saturate deps =
    let _, new_deps = deep_deps deps in
    if new_deps = deps then deps else saturate new_deps in
  let deps = M.mapi (fun key x -> S.remove key @@ fst x) (saturate deps) in
  M.map (fun s -> s |> S.elements |> sort) deps

let add_params : Hflz.fml -> Hflz.var list -> Hflz.fml = fun f params ->
  List.fold_left (fun acc x ->
      Hflz.App (acc, Var x)
    ) f params 

let gen_paramed_types : hes -> Hflz.var list M.t -> Hflz.ty M.t = 
  fun (fs, f) paramed_params ->
    (* let init = List.fold_left (fun m (x, t, _, _) ->
       M.add x t m
       ) M.empty fs in *)
    List.fold_left (fun res (x, t, _, _) ->
        let params = M.find x paramed_params in
        let ts = List.map (fun param ->
            try
              M.find param res
            with Not_found -> failwith @@ Printf.sprintf "%s" (Hflz.string_of_var param)
          ) params in
        let ty = List.fold_right (fun t acc -> Hflz.Arr (Ty t, acc)) ts t in
        M.add x ty res
      ) M.empty fs

let paramed_var : Hflz.var -> Hflz.var = fun (x, q, i) -> (x ^ "'", q, i)

let paramed_vars : Hflz.fml -> S.t -> Hflz.fml = fun f before ->
  (* f の中の変数のうち、before に含まれるものについてのみ paramed_var を適用 *)
  let fv = Hflz.fv f in
  let params = S.inter fv before |> S.elements in
  let paramed = List.map (fun x -> Hflz.Var (paramed_var x)) params in
  List.fold_left2 (fun acc s t -> Hflz.subst t s acc) f params paramed

(* [var -> fml] のマップのうち、before に含まれる物を param したマップを返す *)
let gen_paramed_vars_map : S.t -> Hflz.fml M.t -> Hflz.fml M.t = 
  fun before m -> M.map (fun f -> paramed_vars f before) m

let subst_paramed_vars : Hflz.fml M.t -> Hflz.fml -> Hflz.fml = fun substs f ->
  let rec aux (m : Hflz.fml M.t) : Hflz.fml -> Hflz.fml = function
    | Op (op, f1, f2) -> Op (op, aux m f1, aux m f2)
    | Pred (b, p, fs) -> Pred (b, p, List.map (aux m) fs)
    | Var x -> begin
        try M.find x m with Not_found -> Var x
      end
    | Disj (f1, f2) -> Disj (aux m f1, aux m f2)
    | Conj (f1, f2) -> Conj (aux m f1, aux m f2)
    | Mu (v, ty, f) -> let m = M.remove v m in Mu (v, ty, aux m f)
    | Nu (v, ty, f) -> let m = M.remove v m in Nu (v, ty, aux m f)
    | Lam (v, ety, f) -> let m = M.remove v m in Lam (v, ety, aux m f)
    | App (f1, f2) -> App (aux m f1, aux m f2)
    | Int _ | True | False as e -> e in
  aux substs f

let rec lambdify : Hflz.ty -> Hflz.var list -> Hflz.fml -> Hflz.fml = fun ty vars f ->
  match ty, vars with
  | ty, [] -> f
  | Arr (ety, ty), x::xs -> 
    Lam (paramed_var x, ety, lambdify ty xs f)
  | _ -> failwith "lambdify: hes"

(* parametrize given HES for Coq *)
let parametrize : hes -> hes = fun (feq, f) -> 
  let paramed_params = gen_paramed_params (feq, f) in
  let paramed_types = gen_paramed_types (feq, f) paramed_params in
  let paramed_apps = M.mapi (fun key vars ->
      add_params (Hflz.Var key) vars
    ) paramed_params in
  (* let used_funcs = gen_used_funcs (feq, f) in *)
  (* let string_of_var_list x = 
     Printf.sprintf "[%s]" 
      (List.fold_right (fun x acc -> Printf.sprintf "%s;%s" (Hflz.string_of_var x) acc) x "") in *)
  (* let () = show_M show_S used_funcs |> print_endline in  *)
  let rec aux : S.t -> feq list -> feq list = fun before -> function
    | [] -> []
    | (x, t, fp, body)::fs ->
      let params = M.find x paramed_params in
      let paramed_vars_map = gen_paramed_vars_map before paramed_apps in
      let ty = M.find x paramed_types in
      let body = body 
                 |> subst_paramed_vars paramed_vars_map
                 |> lambdify ty params in
      let feq = (x, ty, fp, body) in
      let feqs = aux (S.add x before) fs in
      feq::feqs in
  (* let () = show_M (Hflz.string_of_fml false) paramed_apps |> print_endline in    *)
  List.rev @@ aux S.empty feq, subst_paramed_vars paramed_apps f

(* split feqs into list of recursive functions and list of others *)
let split_funcs : feq list -> feq list * feq list = fun feqs ->
  let used_funcs = gen_used_funcs (feqs, True) in
  let recs, nots = List.fold_left (fun (rec_f, others) feq ->
      let (f, _, _ , _) = feq in
      if S.is_empty @@ M.find f used_funcs then (* not recursive *)
        (rec_f, feq :: others)
      else
        (feq :: rec_f, others)
    ) ([], []) feqs in
  List.rev recs, List.rev nots

(* [sub_q0_1 -> [];
   sub_q0_0 -> [];
   repeat_q0_1 -> [];
   repeat_q0_0 -> [repeat_q0_1;];
   main_q0_0 -> [repeat_q0_1;sub_q0_1;g_q0_1;input_q0_1;repeat_q0_0;sub_q0_0;g_q0_0;input_q0_0;];
   input_q0_1 -> [];
   input_q0_0 -> [input_q0_1;];
   g_q0_1 -> [sub_q0_1;];
   g_q0_0 -> [repeat_q0_1;sub_q0_1;repeat_q0_0;sub_q0_0;];
   fin_q0_0 -> [];
   ] *)