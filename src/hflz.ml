(* HFLz syntax and utils *)

open Util

(* types are splited into Hflz_type in order to avoid cyclic dependency with Util *)
include Hflz_type

type fml = 
  | Int of int
  | Op of op * fml * fml
  | True
  | False
  | Pred of bool * string * fml list
  | Var of var
  | Disj of fml * fml
  | Conj of fml * fml
  | Mu of var * ty * fml
  | Nu of var * ty * fml
  | Lam of var * ety * fml (* λ x_q_m : ety . f *)
  | App of fml * fml
and ty = 
  | O
  | Arr of ety * ty
and ety = 
  | Ty of ty
  | TInt

let rec string_of_fml typ = function
  | Int i -> string_of_int i
  | Op (op, f1, f2) ->
    sprintf "(%s %s %s)" (string_of_fml typ f1) op (string_of_fml typ f2)
  | True -> "True"
  | False -> "False"
  | Pred (b, pre, fs) -> 
    let pre = if b then pre else "not " ^ pre in
    Printf.sprintf "%s(%s)" pre @@ String.concat ", " (List.map (string_of_fml typ) fs)
  | Var v -> string_of_var v
  | Disj (f1, f2) -> 
    sprintf {|(%s \/ %s)|} (string_of_fml typ f1) (string_of_fml typ f2)
  | Conj (f1, f2) ->
    sprintf {|(%s /\ %s)|} (string_of_fml typ f1) (string_of_fml typ f2)
  | Mu (v, ty, f) ->
    if typ then
      sprintf "(μ %s : %s . %s)" (string_of_var v) (string_of_ty ty) (string_of_fml typ f)
    else
      sprintf "(μ %s. %s)" (string_of_var v) (string_of_fml typ f)
  | Nu (v, ty, f) ->
    if typ then
      sprintf "(ν %s : %s . %s)" (string_of_var v) (string_of_ty ty) (string_of_fml typ f)
    else sprintf "(ν %s. %s)" (string_of_var v) (string_of_fml typ f)
  | Lam (v, ety, f) ->
    if typ then
      sprintf "(λ %s : %s . %s)" (string_of_var v) (string_of_ety ety) (string_of_fml typ f)
    else
      sprintf "(λ %s. %s)" (string_of_var v) (string_of_fml typ f)
  | App (f1, f2) ->
    sprintf "(%s %s)" (string_of_fml typ f1) (string_of_fml typ f2)
and string_of_ty = function
  | O -> "o"
  | Arr (Ty O, ty) -> sprintf "o -> %s" (string_of_ty ty)
  | Arr (TInt, ty) -> sprintf "int -> %s" (string_of_ty ty)
  | Arr (ety, ty) -> 
    begin 
      match ety with
      | Ty _ -> sprintf "(%s) -> %s" (string_of_ety ety) (string_of_ty ty)
      | TInt -> sprintf "int -> %s" (string_of_ty ty)
    end
and string_of_ety = function
  | Ty ty -> string_of_ty ty
  | TInt -> "int"

(* [f/x]e  *)
let rec subst f x e = 
  let su = subst f x in
  match e with
  | Op (op, f1, f2) -> Op (op, su f1, su f2)
  | Pred (b, p, fs) -> Pred (b, p, List.map su fs)
  | Var y when x = y -> f
  | Disj (f1, f2) -> Disj (su f1, su f2)
  | Conj (f1, f2) -> Conj (su f1, su f2)
  | Mu (v, ty, f) when v <> x -> Mu (v, ty, su f)
  | Nu (v, ty, f) when v <> x -> Nu (v, ty, su f)
  | Lam (v, ety, f) when v <> x -> Lam (v, ety, su f)
  | App (f1, f2) -> App (su f1, su f2)
  | Int _ | Var _ | True | False 
  | Mu _ | Nu _ | Lam _ -> e

(* imp x y = not x \/ y *)
(* let imp x y = 
   match x with
   | (Pred (b, p, fs)) -> Disj (Pred (not b, p, fs), y)
   | _ -> failwith "invalid input to imp at hfl.ml" *)

(* module S = Set.Make(struct type t = string let compare = compare end) *)
(* module V = Set.Make (struct type t = var let compare = compare end) *)

let fv (f : fml) : S.t =
  let open S in
  let rec aux binds = function
    | Int _ | True | False -> empty
    | Op (op, f1, f2) -> 
      union (aux binds f1) (aux binds f2)
    | Pred (b, p, fs) ->
      List.fold_left (fun acc b -> union acc (aux binds b)) empty fs
    | Var x -> if mem x binds then empty else singleton x
    | Disj (f1, f2) | Conj (f1, f2) | App (f1, f2) ->
      union (aux binds f1) (aux binds f2)
    | Mu (v, ty, f) | Nu (v, ty, f) -> aux (add v binds) f
    | Lam (v, ety, f) -> aux (add v binds) f
  in aux empty f

let fvl : fml -> var list =
  fun f -> f |> fv |> S.elements

let rec remove_useless_binds = function
  | Op (op, f1, f2) -> Op (op, remove_useless_binds f1, remove_useless_binds f2)
  | Pred (b, p, fs) -> Pred (b, p, List.map remove_useless_binds fs)
  | Disj (f1, f2) -> Disj (remove_useless_binds f1, remove_useless_binds f2)
  | Conj (f1, f2) -> Conj (remove_useless_binds f1, remove_useless_binds f2)
  | Mu (v, ty, f) ->
    if (List.exists ((=) v) (fvl f)) then Mu (v, ty, remove_useless_binds f) else  remove_useless_binds f 
  | Nu (v, ty, f) ->
    if (List.exists ((=) v) (fvl f)) then Nu (v, ty, remove_useless_binds f) else  remove_useless_binds f 
  | Lam (v, ety, f) -> Lam (v, ety, remove_useless_binds f)
  | App (f1, f2) -> App (remove_useless_binds f1, remove_useless_binds f2)
  | True | False | Int _ | Var _ as f -> f

(* beta reduction *)
(* [beta] may cause several beta reductions in one application *)
let rec beta : fml -> fml = function 
  | Op (op, f1, f2) -> Op (op, beta f1, beta f2)
  | Pred (b, p, fs) -> Pred (b, p, List.map beta fs)
  | Disj (f1, f2) -> Disj (beta f1, beta f2)
  | Conj (f1, f2) -> Conj (beta f1, beta f2)
  | Mu (v, ty, f) -> Mu (v, ty, beta f)
  | Nu (v, ty, f) -> Nu (v, ty, beta f) 
  | Lam (v, ety, f) -> Lam (v, ety, beta f)
  | App (Lam (v, ety, f1), f2) -> subst f2 v f1
  | App (f1, f2) -> App (beta f1, beta f2)
  | True | False | Int _ | Var _ as f -> f

let reds f =
  let rec aux f n =
    if n < 0 then 
      f 
    else
      let f2 = beta f in
      if f2 = f then f else aux f2 (n - 1) in
  aux f 5

let rec argt_of_ty : ty -> ety list = function
  | Arr (t, ty) -> t :: (argt_of_ty ty)
  | O -> []

(* get head function name from Apps *)
let get_fun_name : fml -> var = 
  let rec aux = function
    | Var f -> f
    | App (f, _) -> aux f
    | _ -> failwith "get_fun_name: hflsz" in
  aux


(* tests *)

(* let ar1 = Arr (Ty O, O)
   let ar1_2 = Arr (Ty O, ar1)
   let ar1_3 = Arr (Ty O, ar1_2)
   let ar2 = Arr (Ty ar1_3, ar1_3)


   let fai_ab = Nu ("X", ar1, 
                 Lam ("Y", Ty O, 
                      Disj (Var "Y", 
                            Dia ("a", 
                                 App (Var "X", 
                                      Dia ("b", Var "Y"))))))

   let fai_app = App (fai_ab, Var "fai")

   let id = Lam ("x", Ty O, Var "x")
   let fst = Lam ("x", Ty O, Lam ("y", Ty O, Var "x"))
   let snd = Lam ("x", Ty O, Lam ("y", Ty O, Var "y"))

   let test0 () = string_of_fml fai_ab = (subst True "X" fai_ab |> string_of_fml)

   let test1 () = subst True "fai" fai_app |> string_of_fml |> print_string

   let test2 () = beta (App (App (fst, Int 0), Int 1)) |> string_of_fml |> print_endline
   let test3 () = reds (App (App (snd, Int 0), Int 1)) |> string_of_fml |> print_endline *)