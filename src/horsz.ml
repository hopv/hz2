(* target language syntax and utils *)

module Commons = struct
  type var = string
  type op = string

  type ty = O | Arr of ety * ty
  and ety = Ty of ty | TInt 
  [@@deriving show]

  let sprintf = Printf.sprintf

  let rec string_of_ty = function
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

end

include Commons  

type exp =
  | Var of var
  | Int of int
  | Op of op * exp * exp
  | If of pred * exp * exp
  | Cont of string * exp list
  | App of exp * exp
  (* | Lam of var * exp *)
and pred = Pred of bool * string * (exp list)
[@@deriving show]

let rec string_of_exp = function  
  | Var x -> x
  | Int i -> string_of_int i
  | Op (op, e1, e2) ->
    sprintf "%s %s %s" (string_of_exp e1) op (string_of_exp e2)
  | If (p, e1, e2) -> 
    sprintf "if %s then %s else %s" (string_of_pred p) (string_of_exp e1) (string_of_exp e2)
  | Cont (a, es) ->
    Printf.sprintf "%s[%s]" a @@ String.concat ", " (List.map string_of_exp es)
  | App (e1, e2) -> 
    sprintf "(%s %s)" (string_of_exp e1) (string_of_exp e2)
(* | Lam (x, e) -> 
   sprintf "λ%s. %s" x (string_of_exp e) *)
and string_of_pred = function
  | Pred (b, pre, es) -> 
    let pre = if b then pre else "not " ^ pre in
    Printf.sprintf "%s(%s)" pre @@ String.concat ", " (List.map string_of_exp es)

(* Statement (f, xs, t, exp) ==> f xs : t = exp *)
type statement = Statement of string * (var list) * ty * exp

let string_of_statement : statement -> string = 
  fun (Statement (f, vars, ty, e)) ->
    sprintf "%s %s = %s" f 
      (List.fold_left (fun acc x -> sprintf "%s %s" acc x) "" vars)
      (string_of_exp e)

type program = Prog of statement list * exp

let string_of_prog (Prog (stats, e)) = 
  sprintf "({%s\n}, %s)"
    (List.fold_left (fun acc x -> sprintf "%s\n%s;" acc (string_of_statement x)) "" stats)
    (string_of_exp e)

(* type lts = (string * event * string) list *)

(* let show_lts lts = 
   let body = List.fold_left (fun acc (a, b ,c) -> acc ^ sprintf "(%s, %s, %s);\n" a b c) "" lts in
   sprintf "[\n%s]" body *)

(* let split_lts lts : (string list) * (string list) =
   let module S = Set.Make(struct type t = string let compare = compare end) in 
   let open S in
   let nodes = ref empty in
   let labels = ref empty in
   let _ = List.iter (fun (q0, ev, q1) -> nodes := add q0 !nodes; nodes := add q1 !nodes; labels := add ev !labels) lts in
   (elements !nodes, elements !labels) *)

(* tests *)
(* 
let omega = Statement ("omega", ["x"], O, App (Var "omega", Var "x"))

let asrt = Statement ("assert", ["b"], O, 
                      If (Pred (true, "b", []), Unit, Event ("fail", Var "omega")))

let pmain = Statement ("main", ["m"], Arr (TInt, O),
                       App (App(Var "sum", Var "m"), Var "f"))
(* int -> (int -> o) -> o *)
let psum = Statement ("sum", ["n"; "k"], 
                      Arr(TInt, Arr(Ty (Arr(TInt, O)), O)),
                      If (Pred (true, "<=", [Var "n"; Int 0]), App (Var "k", Int 0), App (App (Var "sum", Op ("-", Var "n", Int 1)), App (App (Var "g", Var "n"), Var "k"))))
let pf = Statement ("f", ["r"], Arr (TInt, O),
                    Event ("end", Unit))

(* int -> (int -> o) -> int -> o *)
let pg = Statement ("g", ["n"; "k"; "r"], Arr (TInt, Arr (Ty (Arr (TInt, O)), Arr (TInt, O))),
                    App (Var "k", Op ("+", Var "n", Var "r")))

let sum = Prog ([pmain; psum; pf; pg], App (Var "main", Var "x")) *)


