(* target language syntax and utils *)

include Horsz.Commons

type exp =
  | Var of var * ety
  | Int of int (* TInt *)
  | Op of op * exp * exp (* TInt *)
  | If of pred * exp * exp (* Ty O *)
  | Cont of string * exp list (* Ty O *)
  | App of exp * exp * ty
  | Lam of var * ety * exp * ty (* λ var : ety. exp : ty*)
and pred = Pred of bool * string * (exp list) (* TInts *)
[@@deriving show]

let rec string_of_exp = function  
  | Var (x, ety) -> sprintf "(%s:%s)" x @@ string_of_ety ety
  | Int i -> string_of_int i
  | Op (op, e1, e2) ->
    sprintf "%s %s %s" (string_of_exp e1) op (string_of_exp e2)
  | If (p, e1, e2) -> 
    sprintf "if %s then %s else %s" (string_of_pred p) (string_of_exp e1) (string_of_exp e2)
  | Cont (a, es) ->
    Printf.sprintf "%s(%s)" a @@ String.concat ", " (List.map string_of_exp es)
  | App (e1, e2, ty) -> 
    sprintf "(%s %s : %s)" (string_of_exp e1) (string_of_exp e2) (string_of_ty ty)
  | Lam (x, ety, e, ty) -> 
    sprintf "(λ%s:%s. %s : %s)" x (string_of_ety ety) (string_of_exp e) (string_of_ty ty)
and string_of_pred = function
  | Pred (b, pre, es) -> 
    let pre = if b then pre else "not " ^ pre in
    Printf.sprintf "%s(%s)" pre @@ String.concat ", " (List.map string_of_exp es)

(* Statement (f, xs, t, exp) ==> f : t = λ...exp *)
type statement = Statement of string * ty * exp

let string_of_statement : statement -> string = 
  fun (Statement (f, ty, e)) ->
    sprintf "%s : %s = %s" f (string_of_ty ty)
      (string_of_exp e)

type program = Prog of statement list * exp

let string_of_prog (Prog (stats, e)) = 
  sprintf "({%s\n}, %s)"
    (List.fold_left (fun acc x -> sprintf "%s\n%s;" acc (string_of_statement x)) "" stats)
    (string_of_exp e)

module M = Map.Make (struct 
    type t = var 
    let compare = Stdlib.compare 
  end)

let get_type : exp -> ety = function
  | Var (v, ety) -> ety
  | Int _ -> TInt
  | Op _ -> TInt
  | If _ -> Ty O
  | Cont _ -> Ty O
  | App (_, _, ty) -> Ty ty
  | Lam (_, ety, _, ty) -> Ty (Arr (ety, ty))

let rec type_exp : ety M.t -> Horsz.exp -> exp = 
  fun env -> function
    | Var v -> 
      (* Printf.eprintf "%s [%s]\n" v (M.fold (fun key v acc -> Printf.sprintf "%s = %s; %s" key (string_of_ety v) acc) env ""); *)
      Var (v, M.find v env)
    | App (e1, e2) -> 
      let e1 = type_exp env e1 in
      let e2 = type_exp env e2 in
      begin
        match get_type e1 with
        | Ty (Arr (_, ty)) -> App (e1, e2, ty)
        | _ -> failwith "type_exp: horsz_t"
      end
    | Int i -> Int i
    | Op (op, e1, e2) -> Op (op, type_exp env e1, type_exp env e2)
    | If (Pred(b, p, es), e1, e2) -> 
      If (Pred(b, p, List.map (type_exp env) es), type_exp env e1, type_exp env e2)
    | Cont (a, es) -> Cont (a, List.map (type_exp env) es)

let type_statement : ety M.t -> Horsz.statement -> statement =
  fun env (Statement (f, xs, t, e)) ->
    let rec aux res = function
      | ([], _) -> res
      | (x :: xs, Arr (ety, ty)) -> aux ((x, ety) :: res) (xs, ty) 
      | (x, t) -> 
        failwith @@ Printf.sprintf "type_statement: horsz_t: %s" f in
    let args_t = aux [] (xs, t) in
    let env = List.fold_left (fun acc (x, ety) -> 
        M.add x ety acc
      ) env args_t in
    let e = type_exp env e in
    let e, _ = List.fold_left (fun (acc, t) (x, ety) ->
        Lam (x, ety, acc, Arr (ety, t)),  Arr (ety, t)
      ) (e, O) args_t in
    Statement (f, t, e)

let get_main_type e (ss : Horsz.statement list) =
  let rec main_name : Horsz.exp -> var = function
    | App (f, _) -> main_name f
    | Var x -> x
    | _ -> failwith "main_name: get_main_type: horsz_t" in
  let main = main_name e in
  let Horsz.Statement (_, _, main_t, _) =
    List.find (fun (Horsz.Statement (fn,_,_,_)) -> fn = main) ss in
  main_t

let type_program : Horsz.program -> program = 
  fun (Prog (ss, e)) ->
    let env = List.fold_left (fun acc (Horsz.Statement(f, _, ty, _)) -> 
        M.add f (Ty ty) acc
      ) M.empty ss in
    let rec types res : Horsz.ty -> Horsz.ety list = function
      | Arr (ety, ty) -> types (ety::res) ty
      | O -> List.rev res in
    let rec args res : Horsz.exp -> var list = function
      | App (f, Var x) -> args (x :: res) f
      | _ -> res in
    let main_env = 
      List.fold_left2 
        (fun acc arg t -> M.add arg t acc)
        env (args [] e) (types [] (get_main_type (e) ss)) in
    Prog (List.map (type_statement env) ss, type_exp main_env e)
