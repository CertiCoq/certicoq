open Monad0
open StateMonad
open Cps
open Shrink_cps
open State

type 'x freshM = (unit, 'x) compM

val freshen_term : exp -> int M.t -> exp freshM

val freshen_fun : fundefs -> int M.t -> fundefs freshM
