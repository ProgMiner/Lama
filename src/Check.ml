open OCanren

open Solver


let i0 = !!0
let i1 = !!1
let i2 = !!2

(*
Call(forall ({4, 6, 7, 8, 9, 17, 18, 19}). (
    Call(forall ({}). (T) => ([Int]) -> Int, [Int], tv_6)
    Ind_2(Sexp [B ([tv_17; tv_18; tv_19])], Int)
    Ind_1(Sexp [B ([tv_17; tv_18; tv_19])], Int)
    Ind_0(Sexp [B ([tv_17; tv_18; tv_19])], Int)
    Sexp_B(tv_4, [tv_17; tv_18; tv_19])
    Call(forall ({}). (T) => ([Int]) -> Int, [Int], tv_6)
    Ind_2(Sexp [A ([tv_7; tv_8; tv_9])], Int)
    Ind_1(Sexp [A ([tv_7; tv_8; tv_9])], Int)
    Ind_0(Sexp [A ([tv_7; tv_8; tv_9])], Int)
    Sexp_A(tv_4, [tv_7; tv_8; tv_9])
) => ([tv_4]) -> tv_6
*)

(* Ind_0(Sexp [A ([tv_7; tv_8; tv_9])], Int) *)

let sA = !!"A"

let make_goal ts = ocanren
    { fresh t1, t2, t3 in CTop //-
        CAnd
            ( CIndI (0, TSexp ([(sA, [t1; t2; t3])]), TInt)
            , CAnd
                ( CIndI (1, TSexp ([(sA, [t1; t2; t3])]), TInt)
                , CIndI (2, TSexp ([(sA, [t1; t2; t3])]), TInt)
                )
            )

    & ts == [t1; t2; t3]
    }

(*
let make_goal c' = ocanren
    { fresh t7, t' in subst_c i1 t' (CCall (t7, [TName i1], TName i1)) c' }

let res () = Stream.take ~n:10 @@
    run q make_goal (fun x -> x#reify reify_lama_c)
*)

let res () = Stream.take ~n:10 @@
    run q make_goal (fun x -> x#reify @@ Std.List.reify reify_lama_t)
