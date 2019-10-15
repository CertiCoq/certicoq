
type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

val nzhead : uint -> uint

val unorm : uint -> uint

val norm : unit -> unit

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val succ : uint -> uint

  val double : uint -> uint

  val succ_double : uint -> uint
 end
