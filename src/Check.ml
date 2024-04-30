open OCanren

open Solver


let i0 = !!0
let i1 = !!1
let i2 = !!2

(*
let make_goal ts = ocanren { fresh t in ts == [t] & CTop //- CSexp (i0, t, [t]) }
*)

(*
let make_goal c' = ocanren
    { fresh t7, t' in subst_c i1 t' (CCall (t7, [TName i1], TName i1)) c' }

let res () = Stream.take ~n:10 @@
    run q make_goal (fun x -> x#reify reify_lama_c)
*)

(*
let res () = Stream.take ~n:1 @@
    run q make_goal (fun x -> x#reify @@ Std.List.reify reify_lama_t)
*)

(*
let hook _ v t =
    Printf.printf "occurs check : %d |-> %s\n" v @@ GT.show logic_lama_t t ;
    raise Occurs_check
*)

(*
let make_goal t = ocanren {
    set_occurs_hook_lama_t t &
    fresh ts in t == TSexp [(i1, ts)] & ts == [t]
}
*)

let make_goal t = ocanren { set_occurs_hook_lama_t t & t == TArray t }

let res () = Stream.take ~n:1 @@
    run q make_goal (fun x -> x#reify reify_lama_t)
