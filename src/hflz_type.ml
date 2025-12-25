type op = string
type var = string * string * int (* x_q_m *)
type label = string

let string_of_var (x, q, m) =
  match q with
  | "" -> Printf.sprintf "%s_" x
  | _ -> Printf.sprintf "%s_%s_%d" x q m