
type cterm =
  | CVar of string
  | CInt of int
  | CForall of (cterm list * cterm)  (* forall cterms, cterm *)
  | CExist of (cterm list * cterm)   (* exists cterms, cterm *)
  | CFun of (cterm * cterm * cterm)  (* fun cterm : cterm => cterm *)
  | CAnnot of (cterm * cterm)        (* cterm : cterm *)
  | CImp of (cterm * cterm)          (* cterm -> cterm *)
  | COr of (cterm * cterm)           (* cterm \/ cterm *)
  | CAnd of (cterm * cterm)          (* cterm /\ cterm *)
  | CNot of cterm                    (* ~ cterm *)
  | COp of (string * cterm * cterm)  (* cterm op cterm *)
  | CTrue
  | CFalse
  | CApp of (cterm * (cterm list))   (* cterm cterms *)
  | CAny of string

let rec show_cterm : cterm -> string = function
  | CVar x -> x
  | CInt i -> string_of_int i
  | COp (op, f1, f2) -> "("^show_cterm f1^" "^op^ " "^show_cterm f2^")"
  | CTrue -> "True"
  | CFalse -> "False"
  | COr (f1, f2) -> "("^show_cterm f1 ^ " \\/ " ^ show_cterm f2^")"
  | CAnd (f1, f2) -> "("^show_cterm f1 ^ " /\\ " ^ show_cterm f2^")"
  | CFun (v, ty, f) -> "(fun "^(show_cterm v)^":"^(show_cterm ty)^" => "^show_cterm f^")"
  | CApp (f1, fs) ->
    let args = List.map show_cterm fs in
    "("^show_cterm f1^" "^(List.fold_left (fun x y -> x ^ " " ^ y) "" args)^")"
  | CAnnot (f, ty) -> (show_cterm f) ^": "^ (show_cterm ty)
  | CAny s -> s
  | CNot f -> ("~" ^ show_cterm f)
  | CImp (f1, f2) -> "(" ^ (show_cterm f1) ^ " -> " ^ (show_cterm f2) ^ ")"
  | CForall (qs, f) ->
    (List.fold_left (fun acc x -> acc ^ "forall " ^ (show_cterm x) ^ ", ") "" qs) ^ (show_cterm f)
  | CExist (qs, f) ->
    (List.fold_left (fun acc x -> acc ^ "exists " ^ (show_cterm x) ^ ", ") "" qs) ^ (show_cterm f)

let rec show_cterm_path : cterm -> string = function
  | CVar x -> x
  | CInt i -> string_of_int i
  | COp (op, f1, f2) -> "("^show_cterm_path f1^" "^op^ " "^show_cterm_path f2^")"
  | CTrue -> "top"
  | CFalse -> "bot"
  | COr (f1, f2) -> "("^show_cterm_path f1 ^ " \\/ " ^ show_cterm_path f2^")"
  | CAnd (f1, f2) -> "("^show_cterm_path f1 ^ " /\\ " ^ show_cterm_path f2^")"
  | CFun (v, ty, f) -> "(fun "^(show_cterm_path v)^":"^(show_cterm_path ty)^" => "^show_cterm_path f^")"
  | CApp (f1, fs) ->
    let args = List.map show_cterm_path fs in
    "("^show_cterm_path f1^" "^(List.fold_left (fun x y -> x ^ " " ^ y) "" args)^")"
  | CAnnot (f, ty) -> (show_cterm_path f) ^": "^ (show_cterm_path ty)
  | CAny s -> s
  | CNot f -> ("~" ^ show_cterm_path f)
  | CImp (f1, f2) -> "(" ^ (show_cterm_path f1) ^ " -> " ^ (show_cterm_path f2) ^ ")"
  | CForall (qs, f) ->
    (List.fold_left (fun acc x -> acc ^ "forall " ^ (show_cterm_path x) ^ ", ") "" qs) ^ (show_cterm_path f)
  | CExist (qs, f) ->
    (List.fold_left (fun acc x -> acc ^ "exists " ^ (show_cterm_path x) ^ ", ") "" qs) ^ (show_cterm_path f)

let rec gen_ty : Hflz.ty -> string = function
  (* | O -> "Prop" *)
  | O -> "dom o"
  | Arr (TInt, ty) -> "(nat" ^ " -> " ^ gen_ty ty ^")"
  | Arr (ety, ty) -> "(" ^ gen_ety ety ^ " -> " ^ gen_ty ty ^")"
and gen_ety : Hflz.ety -> string = function
  | Ty ty -> gen_ty ty
  | TInt -> "nat"

let cterm_of_ty : Hflz.ty -> cterm = fun x -> CAny (gen_ty x)
let cterm_of_ety : Hflz.ety -> cterm = fun x -> CAny (gen_ety x)

let rec gen_ty_dom : Hflz.ty -> string = function
  | O -> "o"
  | Arr (TInt, ty) -> "(arint " ^ gen_ty_dom ty ^")"
  | Arr (ety, ty) -> "(ar " ^ gen_ety_dom ety ^ " " ^ gen_ty_dom ty ^ ")"
and gen_ety_dom : Hflz.ety -> string = function
  | Ty ty -> gen_ty_dom ty
  | TInt -> "nat"

let cterm_of_dom : Hflz.ty -> cterm = fun x -> CAny (gen_ty_dom x)  
(* let cterm_of_dome : Hflz.ety -> cterm = fun x -> CAny (gen_ety_dom x)   *)

let rec cterm_of_fml : Hflz.fml -> cterm = function
  | Int i -> CInt i
  | Op (op, f1, f2) -> COp (op, cterm_of_fml f1, cterm_of_fml f2)
  | True -> CTrue
  | False -> CFalse
  | Pred (b, p, fs) -> 
    let body =
      match fs with
      | [] -> CVar p
      | [x] -> CApp (CVar p, [cterm_of_fml x])
      | [lhs ; rhs] -> let lhs, rhs = cterm_of_fml lhs, cterm_of_fml rhs in
        COp (p, lhs, rhs)
      | _ -> CApp (CVar p, List.map (fun x -> cterm_of_fml x) fs)
    in if b then body else CNot body
  | Var x -> CVar (Hflz.string_of_var x)
  | Disj (f1, f2) -> COr (cterm_of_fml f1, cterm_of_fml f2)
  | Conj (f1, f2) -> CAnd (cterm_of_fml f1, cterm_of_fml f2)
  | Mu (v, ty, f) -> failwith "not implemented for now at cterm_of_fml in coq_gen"
  | Nu (v, ty, f) -> failwith "not implemented for now at cterm_of_fml in coq_gen"
  | Lam (v, ety, f) -> CFun (CVar (Hflz.string_of_var v), cterm_of_ety ety, cterm_of_fml f)
  | App (f1, f2) -> CApp(cterm_of_fml f1, [cterm_of_fml f2])

(****************************************************)

let rec cterm_opt : cterm -> cterm = function
  | CAnd (COr (CNot c1, c2), COr (c3, c4)) when c1 = c3 -> CAnd (CImp (cterm_opt c1, cterm_opt c2), CImp (cterm_opt (CNot c3), cterm_opt c4)) 
  | COr (_, CTrue) 
  | COr (CTrue, _) -> CTrue
  | COr (c, CFalse) 
  | COr (CFalse, c) -> c
  | CAnd (c, CTrue) 
  | CAnd (CTrue, c) -> c
  | CAnd (_, CFalse) 
  | CAnd (CFalse, _) -> CFalse
  | CImp (_, CTrue) -> CTrue
  | CImp (CNot c, CFalse) -> c (* ?? *)

  | CVar _ 
  | CInt _
  | CAnnot (_, _)
  | CTrue
  | CFalse
  | CAny _ as c -> c
  | CForall (cs, c) -> CForall (cs, cterm_opt c)
  | CExist (cs, c) -> CExist (cs, cterm_opt c)
  | CFun (c0, c1, c2) -> CFun (c0, c1, cterm_opt c2)
  | CImp (c0, c1) -> CImp (cterm_opt c0, cterm_opt c1)
  | COr (c0, c1) -> COr (cterm_opt c0, cterm_opt c1)
  | CAnd (c0, c1) -> CAnd (cterm_opt c0, cterm_opt c1)
  | CNot c -> CNot (cterm_opt c)
  | COp (s, c0, c1) -> COp (s, cterm_opt c0, cterm_opt c1) 
  | CApp (c, cs) -> CApp (c, List.map cterm_opt cs)

let opts f =
  let rec aux n res = if n < 0 then res else aux (n-1) (cterm_opt res) in
  aux 10 f

type statement =
  | Definition of (string * cterm)
  | Variable of (string * cterm)
  | Theorem of (string * cterm)
  | Ltac of (string * string)
  | Inductive of (string * string)
  | TacticNotation of (string * string)
  | Others of string

let show_statement : statement -> string = function
  | Definition (s, f) -> Printf.sprintf "Definition %s :=\n    %s." s (show_cterm f)
  | Variable (s, f) -> Printf.sprintf "Variable %s : \n    %s." s (show_cterm f)
  | Theorem (s, f) -> Printf.sprintf "Theorem %s:\n     %s." s (show_cterm f)
  | Ltac (n, s) -> Printf.sprintf "Ltac %s :=\n    %s\n" n s
  | Inductive (n, s) -> Printf.sprintf "Inductive %s :=\n    %s.\n" n s    
  | TacticNotation (n, s) -> Printf.sprintf "Tactic Notation %s :=\n    %s.\n" n s
  | Others s -> s

let show_statement_path : statement -> string = function
  | Definition (s, f) -> Printf.sprintf "Definition %s :=\n    %s." s (show_cterm_path f)
  | Variable (s, f) -> Printf.sprintf "Variable %s : \n    %s." s (show_cterm_path f)
  | Theorem (s, f) -> Printf.sprintf "Theorem th_%s:\n     %s." s (show_cterm_path f)
  | Ltac (n, s) -> Printf.sprintf "Ltac %s :=\n    %s" n s
  | Inductive (n, s) -> Printf.sprintf "Inductive %s :=\n    %s." n s    
  | TacticNotation (n, s) -> Printf.sprintf "Tactic Notation %s :=\n    %s." n s
  | Others s -> s


type section = {name : string; variables: statement list; ltacs: statement list; thm: statement}

let show_section : section -> string = fun {name; variables; ltacs; thm} ->
  let str_variables = List.fold_left (fun acc v -> acc ^ "\n  " ^ show_statement v) "" variables in
  let str_ltacs = List.fold_left (fun acc v -> acc ^ "\n  " ^ show_statement v) "" ltacs in (* TODO *)
  let str_thm = show_statement thm in
  Printf.sprintf
    "Section %s.\n  %s\n  %s\n\n  %s\n  Proof.\n\n  (* proof *)\n\n  Qed.\nEnd %s.\n" name str_variables str_ltacs str_thm name

let show_section_split : section -> string * string = 
  fun {name; variables; ltacs; thm} ->
    let str_variables = List.fold_left (fun acc v -> acc ^ "\n  " ^ show_statement v) "" variables in
    let str_ltacs = List.fold_left (fun acc v -> acc ^ "\n  " ^ show_statement v) "" ltacs in (* TODO *)
    let str_thm = show_statement thm in
    let str_sec = Printf.sprintf
        "Section %s.\n  %s\n  Load \"%s_tactics.v\". \n\n  %s\n  Proof.\n\n  (* proof *)\n\n  Qed.\nEnd %s.\n" name str_variables name str_thm name in
    str_sec, str_ltacs

