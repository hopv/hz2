
let sprintf = Printf.sprintf

module S = Set.Make(
  struct
    type t = Hflz_type.var
    let compare = Stdlib.compare
  end)

let show_S : S.t -> string = fun s ->
  sprintf "{%s}" @@
  S.fold (fun elt acc ->
    sprintf "%s,%s" (Hflz_type.string_of_var elt) acc
  ) s ""

module M = Map.Make (struct 
    type t = Hflz_type.var
    let compare = Stdlib.compare 
  end)

let show_M : ('a -> string) -> 'a M.t -> string = fun show_a m ->
  sprintf "[%s]" @@
  M.fold (fun key a acc ->
    sprintf "%s -> %s;\n%s" (Hflz_type.string_of_var key) (show_a a) acc
  ) m ""
