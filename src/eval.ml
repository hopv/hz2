(* open Target

let lookup : (var * statement) list -> var -> exp = fun env v ->
  let rec aux v = function
    | [] -> failwith "lookup error"
    | (x, e)::_ when x = v -> e
    | _::xs -> aux v xs
  in aux x env

type value = VUnit | VBool of bool | VInt of int | VVar of string

let rec eval =
  let events = ref [] in   
  let rec aux env n exp = 
    if n < 0 then () else function
    | Unit -> VUnit
    | Var x -> eval env (n - 1) (lookup env x)
    | Int i -> i
    | Op (s, e1, e2) = let VInt e1, Vint e2 = aux env (n-1) e1, aux env (n-1) e2
        (match s with
          | "+" -> VInt (e1 + e2)
          | "-" -> VInt (e1 - e2))
    | Event (ev, e) -> (events := ev::(!events)); aux env (n-1) e
    | If (pr, e1, e2) -> let VBool pr = aux_pre env (n - 1) pr in
                         aux env (n - 1) (if pr then e1 else e2)
    | App (Var f, e2) -> let fbody = lookup env f in 
  and aux_pre env n (Pred (b, pre, args))
 *)

(* module type TargeExp = sig
  type 'a repr
  type prepr
  val unit : 'a repr
  val var : var -> string repr
  val int : int -> int repr
  val op : string -> int repr -> int repr -> int repr
  val event : string -> 'a repr -> 'b repr
  val _if : prepr -> 'a repr -> 'a repr
  val app : ('a -> 'b) repr -> 'a repr -> 'b repr
  val box : 'a repr -> 'a repr -> 'b repr
  val pred : bool -> string -> int repr list -> 'prepr
end

module TargetExpEval : TargetExp with type 'a repr = ('a * string list) and prepr = bool = struct
  type 'a repr = 'a * string list
  type prepr = bool
  let unit = 
 *)


