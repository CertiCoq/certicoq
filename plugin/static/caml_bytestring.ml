open Byte
open Caml_byte
open Caml_nat

let caml_string_of_bytestring (l : Bytestring.String.t) : string =
  let buf = Bytes.create (caml_int_of_nat (Bytestring.String.length l)) in
  let rec aux i = function
    | Bytestring.String.EmptyString -> ()
    | Bytestring.String.String (c, cs) ->
      Bytes.set buf i (char_of_byte c); aux (succ i) cs
  in
  aux 0 l;
  Bytes.to_string buf
  
let bytestring_of_caml_string (s : String.t) : Bytestring.String.t =
  let rec aux acc i =
    if i < 0 then acc
    else aux (Bytestring.String.String (byte_of_char s.[i], acc)) (i - 1)
  in aux Bytestring.String.EmptyString (String.length s - 1)
  