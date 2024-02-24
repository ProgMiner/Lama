open OCanren

open Solver


let res () = Stream.take ~n:10 @@
    run q (fun ts -> ocanren { fresh t in CTop //- CEq (t, TString) & ts == [t] } )
          (fun x -> x#reify @@ Std.List.reify reify_lama_t)
