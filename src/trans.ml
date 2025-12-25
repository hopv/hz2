
let range n = (* [0; 1; .. n] *)
  let rec aux n x =
    if n = 0 then 0 :: x
    else aux (n - 1) (n :: x)
  in aux n []

let rec trans_exp : Apt.apt -> Apt.state -> int -> Horsz_t.exp -> Hflz.fml = fun apt q m ->
  function
  | Int i -> Int i
  | Var (v, TInt) -> Var (v, "", -1)
  | Var (v, _) -> Var (v, q, m)
  | Op (op, e1, e2) -> Op (op, trans_exp apt q m e1, trans_exp apt q m e2)
  | If (Pred(b, p, es), e1, e2) ->
    let es = List.map (trans_exp apt q m) es in
    Disj (Conj((Pred (b, p, es)), (trans_exp apt q m e1)), 
          Conj((Pred (not b, p, es)), (trans_exp apt q m e2)))
  | App (e1, e2, _) -> begin
      match Horsz_t.get_type e2 with
      | TInt -> App (trans_exp apt q m e1, trans_exp apt q m e2)
      | _ ->
        let t1 = trans_exp apt q m e1 in
        let t2s = List.map (fun qi -> 
            List.map 
              (fun n -> trans_exp apt qi (max m n) e2)
              (range apt.Apt.max_priority)
          ) apt.Apt.states |> List.flatten in
        List.fold_left (fun acc x -> Hflz.App (acc, x)) t1 t2s 
    end
  | Lam (x, ety, e, t) -> begin
      match ety with
      | TInt -> Lam ((x, "", -1), trans_ety apt ety, trans_exp apt q m e)
      | _ ->
        let t = trans_exp apt q m e in
        let args = List.map (fun qi -> 
            List.map
              (fun n -> (x, qi, n), trans_ety apt ety)
              (range apt.Apt.max_priority)
          ) apt.Apt.states |> List.flatten in
        List.fold_right 
          (fun (x, ety) acc -> Hflz.Lam (x, ety, acc))
          args t
    end
  | Cont (a, es) -> 
    let fold f a = function
      | [] -> a
      | [x] -> x
      | x :: xs -> List.fold_left f x xs in
    let aux l =
      fold (fun acc x -> Hflz.Conj (acc, x)) True 
        (List.map (fun (dij, qij) ->
             let t_dij = List.nth es (dij - 1) in
             let m = max m (List.assoc qij apt.Apt.priority) in
             trans_exp apt qij m t_dij
           ) l) in
    fold (fun acc si -> Hflz.Disj (acc, si)) False 
      (List.map aux (List.assoc (q, a) apt.Apt.trans))

and trans_ty : Apt.apt -> Horsz_t.ty -> Hflz.ty = fun apt -> function
  | O -> O
  | Arr (TInt, ty) -> Arr (TInt, trans_ty apt ty)
  | Arr (ety, ty) -> 
    let ety = trans_ety apt ety in
    let rec aux n x =
      if n = 0 then x else aux (n - 1) (Hflz.Arr (ety, x)) in
    let km1 = List.length apt.Apt.states * (1 +  apt.Apt.max_priority) in
    aux km1 (trans_ty apt ty) 
and trans_ety : Apt.apt -> Horsz_t.ety -> Hflz.ety = fun apt -> function
  | Ty ty -> Hflz.Ty (trans_ty apt ty)
  | TInt -> Hflz.TInt

(* let rec lambdify : Apt.apt -> Apt.state -> int -> Horsz.var list -> Horsz.ty -> Horsz.exp -> Hflz.fml = 
   fun apt q m args ty e -> match (args, ty) with
    | ([], ty) -> trans_exp apt q m e
    | (x::xs, Arr(ety, ty)) -> 
      let t = lambdify apt q m xs ty e in
      List.fold_right (fun x acc -> Hflz.Lam (x, trans_ety apt ety, acc)) 
        ((List.map (fun qi -> 
             (List.map (fun n ->
                  (x, qi, n)
                ) (range (apt.Apt.max_priority + 1))
             )) apt.Apt.states) |> List.flatten)
        t
    | _ -> failwith "lambdify: trans" *)

(* [trans_statement _ j statement] is a map from fi to Eij *)
let trans_statement : Apt.apt -> int -> Horsz_t.statement -> Hes.feq list = 
  fun apt j (Statement (fi, ty, e)) ->
    let alpha = if j mod 2 = 0 then Hes.Nu else Hes.Mu in
    List.map (fun q -> 
        ((fi, q, j), trans_ty apt ty, alpha, trans_exp apt q 0 e)
      ) apt.Apt.states

let trans_program : Apt.apt -> Horsz_t.program -> Hes.hes = fun apt (Horsz_t.Prog (ss, e)) ->
  let rg = List.rev @@ range apt.max_priority in
  let es =
    List.map (fun j ->
        List.map (fun fi -> trans_statement apt j fi) ss |> List.flatten
      ) rg |> List.flatten in
  (es, trans_exp apt apt.Apt.initial_state 0 e)

(* tests *)

(* let test () = 
   hes_of_tar `May Target.sum |> Hes.show_hes |> print_endline *)

(* let () = test () *)