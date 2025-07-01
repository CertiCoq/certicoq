let certicoq_debug = ref true

let camlstring_of_coqstring (s: char list) =
  let r = Stdlib.Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Stdlib.Bytes.set r pos c; fill (pos + 1) s
  in Stdlib.Bytes.to_string (fill 0 s)

let certicoq_msg_debug s =
  if !certicoq_debug then
    Feedback.msg_debug (Pp.str (camlstring_of_coqstring s))
