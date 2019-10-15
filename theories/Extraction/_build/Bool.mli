
val bool_dec : bool -> bool -> bool

val eqb : bool -> bool -> bool

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect
