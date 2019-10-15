
type 'a coq_exception =
| Exc of char list
| Ret of 'a

val ret : 'a1 -> 'a1 coq_exception

val raise : char list -> 'a1 coq_exception

val bind :
  'a1 coq_exception -> ('a1 -> 'a2 coq_exception) -> 'a2 coq_exception
