open OCanren

open Solver


let i0 = !!0
let i1 = !!1
let i2 = !!2

let sA = !!"A"

let make_goal ts = ocanren { fresh t in ts == [t] & CTop //- CSexpX (sA, t, [t]) }

(*
let make_goal c' = ocanren
    { fresh t7, t' in subst_c i1 t' (CCall (t7, [TName i1], TName i1)) c' }

let res () = Stream.take ~n:10 @@
    run q make_goal (fun x -> x#reify reify_lama_c)
*)

let res () = Stream.take ~n:1 @@
    run q make_goal (fun x -> x#reify @@ Std.List.reify reify_lama_t)
