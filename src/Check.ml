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

(* Call(forall ({}). ([]) => ([Int]) -> Int, [Int], tv_17) *)
let make_goal c ts = ocanren {
    fresh t1 in ts == [t1] & c //- [CCall (TArrow ([], [], [TInt], TInt), [TInt], t1)]
}

let print_res (c, ts) =
    print_endline @@ "c  = " ^ GT.show GT.list Typing.Type.show_c c ;
    print_endline @@ "ts = " ^ GT.show GT.list Typing.Type.show_t ts

let project_res (c, ts) =
    try
        let get_sexp = string_of_int in
        let c = List.map (project_c get_sexp) @@ logic_list_to_ground logic_lama_c_to_ground c in
        let ts = List.map (project_t get_sexp) @@ logic_list_to_ground logic_lama_t_to_ground ts in
        Some (c, ts)
    with Failure x -> print_endline @@ "Failure: " ^ x ; None

let res () = Stream.iter print_res @@ Stream.map Option.get @@ Stream.filter Option.is_some
    @@ Stream.map project_res @@ run qr make_goal (fun c ts ->
        c#reify @@ Std.List.reify reify_lama_c, ts#reify @@ Std.List.reify reify_lama_t)
