open Coq

let ltac_rd name = 
  let body = Printf.sprintf "apply FP%s; unfold %sgen." name name in
  Ltac ("rd_" ^ name, body)

let ltac_hred rds =
  let rds = List.fold_left (fun acc rd ->
      match rd with
      | Ltac (rd, _) -> Printf.sprintf "%s |\n %s" acc rd
      | _ -> failwith "ltac_hred: coq_ltac"
    ) "red" rds in
  Ltac ("hred", Printf.sprintf "first [%s |\nsimpl]; simpl." rds)

let ltac_pr_br name f =
  let fixname, argt, fp = match f with
  | Hflz.Mu(v, ty, _) -> Hflz.string_of_var v, Hflz.argt_of_ty ty, `Mu
  | Hflz.Nu(v, ty, _) -> Hflz.string_of_var v, Hflz.argt_of_ty ty, `Nu
  | _ -> failwith "invalid argument : ltacs_for_var"
  in
  let arg_num = List.length argt in
  let args = 
    let rec aux n = if n = 0 then "" else "_ " ^ (aux (n-1)) in
    aux arg_num in
  (* let args = match tr with `Path -> args ^ "_" | _ -> args in *)
  let fix_br = Printf.sprintf "  | (%s %s) => hred; pr_%s_rec 2 m" fixname args name in
  let ord_br = 
    match fp with
    | `Nu -> Printf.sprintf 
      "  | |- ord %st _ %s => apply GFP%s; (try unfold %sgen); pr_%s_rec fst m\n  | |- mono %st (%sgen _) => unfold mono; rewrite mono_exp2 in M%sgen; pr_%s_rec fst m"
        fixname fixname fixname fixname name fixname fixname fixname name
    | `Mu -> "" in
  (fix_br, ord_br)
  (* let ord_br = Printf.sprintf 
  "  | |- ord %st _ %s => apply %s; (try unfold %sgen); pr_%s_rec fst m\n  | |- mono %st (%sgen _) => unfold mono; rewrite mono_exp2 in M%sgen; pr_%s_rec fst m"
  fixname fixname ((match fp with | `Mu -> "LFP" | `Nu -> "GFP") ^ fixname ) fixname 
  name fixname fixname fixname name  *)
  

let ltac_unfolds = function
  | [] -> ""
  | labels -> 
    let body = List.fold_left (fun acc x -> acc ^ "label_" ^ x ^ ", ") "" labels in
    Printf.sprintf "unfold %s top, bot;" body

let ltac_pr_unfold_mono name n =
  let base x = Printf.sprintf "  | |- mono ?t %s => (try unfold t); unfold f; unfold mono; pr_%s_rec fst m\n" x name in
  let rec aux m fs res =
    if m < 0 then res
    else 
    let br = base @@ Printf.sprintf "(%s)" fs in
    let fs = Printf.sprintf "%s _" fs in
    aux (m - 1) fs (res ^ br)
  in 
  Printf.sprintf 
  "%s  | |- ord ?t _ _ => (try unfold t); hord; pr_%s_rec fst m\n  | |- ord _ _ _ => hord; pr_%s_rec fst m\n  | |- mono ?t _ => (try unfold t); unfold mono; pr_%s_rec fst m"
  (aux n "?f" "")
  name name name

let ltac_pr_rec name fix_brs_str ord_brs_str unfold_mono_str =
  Ltac ("pr_"^name^"_rec"^" fst n",
        Printf.sprintf        
          {|match n with
| O => idtac ""
| S ?m => 
  auto; try omega;
  match goal with
  | |- _ \/ True => right; auto
  | |- True \/ _ => left; auto
  | |- _ \/ False => left; pr_%s_rec fst m
  | |- False \/ _ => right; pr_%s_rec fst m
  | H : _ /\ _ |- _ => decompose [and] H; clear H; pr_%s_rec fst m
  | H : _ |- ?x => match fst with
                   | 1 => match x with%s
                          (* fix here *)
                          | _ => fail
                          end
                   | _ => fail
                   end
  | |- _ -> _ => intro; pr_%s_rec fst m
  | |- _ /\ _ => split; pr_%s_rec fst m%s
%s
  | Hk : _ -> ?k _ |- ?k _ => apply Hk; pr_%s_rec fst m
  | Hk : _ -> _ -> ?k _ |- ?k _ => apply Hk; pr_%s_rec fst m
  | H : _ -> _ |- _ => last H; pr_%s_rec fst m
  | |- ?H0 \/ ?H1 => (left; pr_%s_rec fst m || right; pr_%s_rec fst m)
  | _ => hred; pr_%s_rec fst m
  end
end.|} name name name fix_brs_str name name ord_brs_str unfold_mono_str name name name name name name)

(* let ltac_pr name =
  Ltac ("pr_"^name^" cs n",
        Printf.sprintf 
          {|match type of cs with
          | ltac_No_arg =>  match type of n with
                            | ltac_No_arg => pr_%s_rec 1 2 1 30
                            | _ => pr_%s_rec 1 2 1 n
                            end
          | _ => match type of n with
                  | ltac_No_arg => pr_%s_rec 1 2 cs 30
                  | _ => pr_%s_rec 1 2 cs n
                  end
          end.|} name name name name) *)

let ltac_hauto name =
  Ltac ("hauto", Printf.sprintf "solve [pr_%s_rec 1 30]." name)

(* let ltac_pr_try name =
  Ltac ("pr_"^name^"_try cs n",
        Printf.sprintf 
          {|match type of cs with
          | ltac_No_arg =>  match type of n with
                            | ltac_No_arg => pr_%s_rec 1 1 1 30
                            | _ => pr_%s_rec 1 1 1 n
                            end
          | _ => match type of n with
                  | ltac_No_arg => pr_%s_rec 1 1 cs 30
                  | _ => pr_%s_rec 1 1 cs n
                  end
          end.|} name name name name) *)

(* let tactic_notation_pr0 name =
  TacticNotation (Printf.sprintf {|"pr_%s" constr(x) constr(y)|} name, Printf.sprintf {|pr_%s x y|} name) *)
(* let tactic_notation_pr1 name =
  TacticNotation (Printf.sprintf {|"pr_%s" constr(x)|} name, Printf.sprintf {|pr_%s x ltac_no_arg|} name) *)
(* let tactic_notation_pr2 name =
    TacticNotation (Printf.sprintf {|"pr_%s"|} name, Printf.sprintf {|pr_%s ltac_no_arg ltac_no_arg|} name) *)

(* let tactic_notation_pr_try0 name =
  TacticNotation (Printf.sprintf {|"pr_%s_try" constr(x) constr(y)|} name, Printf.sprintf {|pr_%s_try x y|} name)
let tactic_notation_pr_try1 name =
  TacticNotation (Printf.sprintf {|"pr_%s_try" constr(x)|} name, Printf.sprintf {|pr_%s_try x ltac_no_arg|} name)
let tactic_notation_pr_try2 name =
    TacticNotation (Printf.sprintf {|"pr_%s_try"|} name, Printf.sprintf {|pr_%s_try ltac_no_arg ltac_no_arg|} name)     *)

let ltacs name (feqs : Hes.feq list) =
  let vars = List.map (fun (v, _, _ ,_) -> Hflz.string_of_var v) feqs in
  let ltac_rds = List.map ltac_rd vars in
  let ltac_hred = ltac_hred ltac_rds in
  let unfold_mono = ltac_pr_unfold_mono name 5 in
  (* 5 shold be the largest order of program *) 
  let fbr, obr = List.split 
      (List.map (fun (v, ty, fp, f) ->
           ltac_pr_br name 
             (match fp with
              | Hes.Nu -> Hflz.Nu (v, ty, f)
              | Hes.Mu -> Hflz.Mu (v, ty, f))) 
          feqs) in  
  let fbr = List.fold_left (fun acc x -> acc ^ "\n                        " ^ x) "" fbr in
  let obr = List.fold_left (fun acc x -> acc ^ "\n" ^ x) "" obr in
  let ltac_pr_rec = ltac_pr_rec name fbr obr unfold_mono in 
  let ltac_hauto = ltac_hauto name in
  (* let ltac_pr = ltac_pr name in
  let ltac_pr_try = ltac_pr_try name in  
  let ltac_tactic_notation0 = tactic_notation_pr0 name in
  let ltac_tactic_notation1 = tactic_notation_pr1 name in
  let ltac_tactic_notation2 = tactic_notation_pr2 name in
  let ltac_tactic_notation_try0 = tactic_notation_pr_try0 name in
  let ltac_tactic_notation_try1 = tactic_notation_pr_try1 name in
  let ltac_tactic_notation_try2 = tactic_notation_pr_try2 name in *)
  ltac_rds @ 
  [ltac_hred; ltac_pr_rec; ltac_hauto]
  (* [ltac_hred; ltac_pr_rec; ltac_pr; ltac_pr_try; ltac_tactic_notation0;ltac_tactic_notation1; ltac_tactic_notation2; ltac_tactic_notation_try0;ltac_tactic_notation_try1; ltac_tactic_notation_try2] *)
