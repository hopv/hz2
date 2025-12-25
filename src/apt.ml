
type state = string

type states = state list

type alphabet = (string * int) list

type trans = (state * string) * ((int * string) list) list

type priority = (state * int) list

type apt = { states : states;
             alphabet : alphabet;
             initial_state : state;
             trans : trans list;
             priority : priority; 
             max_priority : int
           }

let max_priority p =
  List.fold_left (fun acc (_, p) -> max p acc) 0 p

let string_of_states states =
  Printf.sprintf "{%s}" @@ String.concat ", " states

let string_of_alphabet alphabet =  
  Printf.sprintf "{%s}" @@ String.concat ", " 
  @@ List.map (fun (s, i) -> Printf.sprintf "(%s -> %d)" s i) alphabet

let string_of_trans : trans -> string = fun ((x, y), transs) ->
  let aux xx = Printf.sprintf "{%s}" @@ String.concat ", " 
    @@ List.map (fun (i, s) -> Printf.sprintf "(%d, %s)" i s) xx in
  Printf.sprintf "(%s, %s) => {%s}" x y @@ String.concat ", " 
  @@ List.map aux transs

let string_of_transs : trans list -> string = fun ts ->
  Printf.sprintf "{%s}" @@ String.concat ",\n" 
  @@ List.map string_of_trans ts

let string_of_priority priority =
  Printf.sprintf "{%s}" @@ String.concat ", " 
  @@ List.map (fun (s, i) -> Printf.sprintf "(%s -> %d)" s i) priority

let string_of_apt {states; alphabet; initial_state; trans; priority} =
  Printf.sprintf "{\n%s\n%s\n%s\n%s\n%s\n}" 
    (string_of_states states)
    (string_of_alphabet alphabet)
    initial_state
    (string_of_transs trans)
    (string_of_priority priority)