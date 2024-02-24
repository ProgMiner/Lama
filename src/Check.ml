open OCanren

open Solver


(*
let i12 = !!12
let i13 = !!13
let i14 = !!14
let i16 = !!16
let i17 = !!17
let i18 = !!18
let i19 = !!19
let i20 = !!20
let i24 = !!24
let i25 = !!25
let i26 = !!26
let i27 = !!27

let make_goal ts = ocanren
    { fresh t5, t6, t7 in CTop //- CAnd
        ( CEq (t5, TArrow
            ( [i12; i13; i14]
            , CAnd
                ( CCall (TArrow ([], CTop, [TInt], TInt), [TInt], TName i12)
                , CAnd
                    ( CCall (TArrow ([], CTop, [TInt], TInt), [TInt], TName i13)
                    , CCall (TArrow ([], CTop, [TInt], TInt), [TInt], TName i14)
                    )
                )
            , []
            , TName i14
            ))
        , CAnd
            ( CEq (t6, TArrow
                ( [i16; i17; i18; i19; i20]
                , CAnd
                    ( CCall (TArrow ([], CTop, [TInt], TInt), [TInt], TName i16)
                    , CAnd
                        ( CCall (t5, [], TName i17)
                        , CAnd
                            ( CCall (TArrow ([], CTop, [TInt], TInt), [TInt], TName i18)
                            , CAnd
                                ( CCall (t7, [TInt], TName i19)
                                , CCall (t5, [], TName i20)
                                )
                            )
                        )
                    )
                , [TInt]
                , TName i20
                ))
            , CAnd
                ( CEq (t7, TArrow
                    ( [i24; i25; i26; i27]
                    , CAnd
                        ( CCall (TArrow ([], CTop, [TInt], TInt), [TInt], TName i24)
                        , CAnd
                            ( CCall (t5, [], TName i25)
                            , CAnd
                                ( CCall (t6, [TInt], TName i26)
                                , CCall (t5, [], TName i27)
                                )
                            )
                        )
                    , [TInt]
                    , TName i27
                    ))
                , CTop
                )
            )
        )
    & ts == [t5; t6; t7]
    }
*)

let i19 = !!19
let i26 = !!26

let make_goal ts = ocanren
    { fresh t6, t7 in CTop //- CAnd
        ( CEq (t6, TArrow ([i19], CCall (t7, [TInt], TName i19), [TInt], TInt))
        , CEq (t7, TArrow ([i26], CCall (t6, [TInt], TName i26), [TInt], TInt))
        )
    & ts == [t6; t7]
    }

let res () = Stream.take ~n:10 @@
    run q make_goal (fun x -> x#reify @@ Std.List.reify reify_lama_t)
