open Coq

let fresh_id = fun () -> 
  let id = ref 0 in
  fun x -> (id := !id + 1;x ^ string_of_int !id)
let fresh_id = fresh_id ()


let gen_direct_defs : Hes.feq -> statement = fun (fixname, ty, fp, f) ->
  let body = cterm_of_fml f in
  Definition (Hflz.string_of_var fixname, body)

let gen_fix_defs : Hes.feq -> statement list = fun (fixname, ty, fp, f) ->
  let aux fixname ty f lg =
    let domtname = fixname ^ "t" in
    let domt = cterm_of_dom ty in
    let dom = CApp (CVar "dom", [CVar domtname]) in
    let domdef = Definition (domtname, domt) in
    let genname = fixname ^ "gen" in
    (* let qname = fresh_id "q" in *)
    let genbody = CFun (CVar fixname, dom, opts (cterm_of_fml f)) in
    let gendef = Definition (genname, genbody) in
    let fixvar = Variable (fixname, dom) in
    let monovar = Variable ("M" ^ fixname, CVar (Printf.sprintf "mono %s %s" domtname fixname)) in
    (* let monogenvar = Variable ("M" ^ genname, CVar (Printf.sprintf "mono (ar %s %s) %s" domtname domtname genname)) in *)
    (* let monogenvar = Variable ("M" ^ genname, CVar (Printf.sprintf {|forall y z : dom %s,
       mono %s y -> mono %s z -> ord %s y z -> ord %s (%s y) (%s z)|} domtname domtname domtname domtname domtname genname genname)) in *)
    let monogenvar = Variable ("M" ^ genname, CVar (Printf.sprintf {|mono (ar %s %s) %s|} domtname domtname genname)) in
    let fpvar = 
      let arg_names = (Hflz.argt_of_ty ty) |> List.map (fun x -> (fresh_id "arg", x)) in
      let args = List.map (fun (x, y) -> (x, cterm_of_ety y)) arg_names in
      (* add monotonicity of args unless its int *)
      let argsdom =  List.fold_right (fun (x, y) acc -> 
          match gen_ety_dom y with
          | "nat" -> acc
          | z -> (x, CAny z) :: acc
        ) arg_names [] in
      (* |> List.map (fun x -> (fresh_id "arg", cterm_of_dome x)) in *)
      let vars = List.map (fun x -> CVar (fst x)) args in
      let lhs = CApp (CVar fixname, vars) in
      let rhs = CApp (CVar genname, CVar fixname :: vars) in
      let qs = List.map (fun (x, y) -> CAnnot(CVar x, y)) args in
      let mono_args = List.fold_right (fun (arg, argt) acc -> 
          CImp (CApp (CVar "mono", [argt; CVar arg]), acc)) 
          argsdom (COp("<->", lhs, rhs)) in
      Variable ("FP" ^ fixname, CForall (qs, mono_args)) in
    let lfpvar =
      let sp = Printf.sprintf in
      let id = fresh_id "arg" in
      let genapp = sp "(%s %s)" genname id in
      let fp = match lg with | `LFP -> "LFP" | `GFP -> "GFP" in
      let str1, str2 = match lg with
        | `LFP -> (genapp ^ " " ^ id, fixname ^ " " ^ id)
        | `GFP -> (id ^ " " ^ genapp, id ^ " " ^ fixname) in
      Variable (fp^fixname, 
                CForall ([CAnnot(CVar id, dom)],
                         CVar (sp
                                 {| mono %s %s
                                    -> ord %s %s
                                    -> ord %s %s|} domtname id domtname str1 domtname str2 ))) in
    [domdef; gendef; fixvar; monovar; monogenvar; fpvar; lfpvar]
  in 
  aux (Hflz.string_of_var fixname) ty f 
    (match fp with Mu -> `LFP | Nu -> `GFP)

(* let bind_forall : Hflz.fml -> Hflz.ty -> Hflz.fml = fun f ty -> 
   let rec aux res : Hflz.ty -> string list = function
    (* | Arr (ety, ty) -> aux ((fresh_id "arg", ety)::res) ty *)
    | Arr (ety, ty) -> aux ((fresh_id "arg")::res) ty
    | O -> res in
   let binds = aux [] ty in
   List.fold_left (fun acc x ->
      Hflz.App (acc, Hflz.Var (x, "", -1))
    ) f binds *)

let section_of_hes name : Hes.hes -> section = fun (feqs, f) ->
  let vars = List.map (fun (v, _, _ ,_) -> Hflz.string_of_var v) feqs in
  let rec_feqs, not_rec_feqs = Hes.split_funcs feqs in
  let variables = List.fold_left (fun acc x ->
      acc @ [gen_direct_defs x]
    ) [] not_rec_feqs in
  let variables = 
    List.fold_left (fun acc x -> 
        acc @ (gen_fix_defs x)
      ) variables rec_feqs in
  let ltacs = Coq_ltac.ltacs name rec_feqs in
  let thm = 
    let thmname = Printf.sprintf "%s" name in
    let fvars = List.map (fun x -> CVar x) (List.filter (fun x -> not (List.mem x vars)) (List.map Hflz.string_of_var @@ Hflz.fvl f)) in
    (* |> fun x -> (match tr with `Path -> x @ [CVar "q"] | _ -> x) in *)
    (* let (_, main_t, _, _) =
       List.find (fun (fn,_,_,_) -> Hflz.Var fn = f) feqs in
       let f = bind_forall f main_t in *)
    let thmbody = opts (cterm_of_fml f) in
    Theorem(thmname, CForall (fvars, thmbody)) in
  {name; variables; ltacs; thm}