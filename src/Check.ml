open OCanren

open Solver


let i13 = !!13
let i14 = !!14

let make_goal ts = ocanren
    { fresh t23 in CTop //-
        CCall (TArrow
            ( [i13; i14]
            , CCall (TArrow ([], CTop, [TInt], TInt), [TName i13], TName i14)
            , [TName i13]
            , TName i14), [TInt], t23)
    & ts == [t23]
    }

let res () = Stream.take ~n:1 @@
    run q make_goal (fun x -> x#reify @@ Std.List.reify reify_lama_t)
