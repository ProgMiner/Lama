
module OrigList = List

open GT

open OCanren
open OCanren.Std


@type ('a5, 'a4, 'a3, 'a2, 'a1, 'a0) lama_t =
| TName of 'a5
| TInt
| TString
| TArrow of 'a4 * 'a3 * 'a2 * 'a1
| TArray of 'a1
| TSexp of 'a0
with show, compare, foldl, gmap

@type ('a4, 'a3, 'a2, 'a1, 'a0) lama_c =
| CTop
| CAnd of 'a4 * 'a4
| CEq of 'a0 * 'a0
| CBox of 'a0
| CFun of 'a0
| CInd of 'a0 * 'a0
| CIndI of 'a3 * 'a0 * 'a0
| CSexp of 'a0
| CSexpX of 'a2 * 'a0 * 'a1
| CCall of 'a0 * 'a1 * 'a0
with show, compare, foldl, gmap

@type ground_lama_t =
    ( int
    , int List.ground
    , ground_lama_c
    , ground_lama_t List.ground
    , ground_lama_t
    , (string * ground_lama_t List.ground) List.ground
    ) lama_t
and ground_lama_c =
    ( ground_lama_c
    , Nat.ground
    , string
    , ground_lama_t List.ground
    , ground_lama_t
    ) lama_c
with show, compare, foldl, gmap

@type logic_lama_t =
    ( int logic
    , int logic List.logic
    , logic_lama_c
    , logic_lama_t List.logic
    , logic_lama_t
    , (string logic * logic_lama_t List.logic) logic List.logic
    ) lama_t logic
and logic_lama_c =
    ( logic_lama_c
    , Nat.logic
    , string logic
    , logic_lama_t List.logic
    , logic_lama_t
    ) lama_c logic
with show, compare, foldl, gmap

type injected_lama_t =
    ( int ilogic
    , int ilogic List.injected
    , injected_lama_c
    , injected_lama_t List.injected
    , injected_lama_t
    , (string ilogic * injected_lama_t List.injected) ilogic List.injected
    ) lama_t ilogic
and injected_lama_c =
    ( injected_lama_c
    , Nat.injected
    , string ilogic
    , injected_lama_t List.injected
    , injected_lama_t
    ) lama_c ilogic


let tName x0 = OCanren.inj (TName x0)
let tInt () = OCanren.inj TInt
let tString () = OCanren.inj TString
let tArrow x0 x1 x2 x3 = OCanren.inj (TArrow (x0, x1, x2, x3))
let tArray x0 = OCanren.inj (TArray x0)
let tSexp x0 = OCanren.inj (TSexp x0)

let cTop () = OCanren.inj CTop
let cAnd x0 x1 = OCanren.inj (CAnd (x0, x1))
let cEq x0 x1 = OCanren.inj (CEq (x0, x1))
let cBox x0 = OCanren.inj (CBox x0)
let cFun x0 = OCanren.inj (CFun x0)
let cInd x0 x1 = OCanren.inj (CInd (x0, x1))
let cIndI x0 x1 x2 = OCanren.inj (CIndI (x0, x1, x2))
let cSexp x0 = OCanren.inj (CSexp x0)
let cSexpX x0 x1 x2 = OCanren.inj (CSexpX (x0, x1, x2))
let cCall x0 x1 x2 = OCanren.inj (CCall (x0, x1, x2))

let reify_lama_t
    (reify_lama_c : (injected_lama_t, logic_lama_t) Reifier.t
                  -> (injected_lama_c, logic_lama_c) Reifier.t)
    : (injected_lama_t, logic_lama_t) Reifier.t =
    let open Env.Monad in
    let open Syntax in

    let* reify_list = List.reify Reifier.reify in
    let* reify_string = Reifier.reify in
    let* reify_int = Reifier.reify in

    Reifier.fix (fun self ->
        let* reify_lama_c = reify_lama_c self in
        let* reify_lama_t_list = List.reify self in
        let* self = self in

        let* reify_sexp = List.reify (
            Reifier.compose Reifier.reify (
                let rec f = function
                | Var (i, xs) -> Var (i, Stdlib.List.map f xs)
                | Value (x, ts) -> Value (reify_string x, reify_lama_t_list ts)
                in

                return f
            )
        ) in

        Reifier.compose Reifier.reify (
            let rec f = function
            | Var (i, xs) -> Var (i, Stdlib.List.map f xs)
            | Value x -> Value (GT.gmap lama_t
                reify_int
                reify_list
                reify_lama_c
                reify_lama_t_list
                self
                reify_sexp
                x)
            in

            return f
        )
    )

let reify_lama_c
    (reify_lama_t : (injected_lama_t, logic_lama_t) Reifier.t)
    : (injected_lama_c, logic_lama_c) Reifier.t =
    let open Env.Monad in
    let open Syntax in

    let* reify_nat = Nat.reify in
    let* reify_string = Reifier.reify in
    let* reify_lama_t_list = List.reify reify_lama_t in
    let* reify_lama_t = reify_lama_t in

    Reifier.fix (fun self ->
        let* self = self in

        Reifier.compose Reifier.reify (
            let rec f = function
            | Var (i, xs) -> Var (i, Stdlib.List.map f xs)
            | Value x -> Value (GT.gmap lama_c
                self
                reify_nat
                reify_string
                reify_lama_t_list
                reify_lama_t
                x)
            in

            return f
        )
    )

let reify_lama_t = reify_lama_t reify_lama_c
let reify_lama_c = reify_lama_c reify_lama_t

let rec logic_nat_to_ground : Nat.logic -> Nat.ground = function
| Var _ -> failwith "variable nat"
| Value Nat.O -> Nat.O
| Value (Nat.S x) -> Nat.S (logic_nat_to_ground x)

let rec logic_list_to_ground (f : 'a -> 'b) : 'a List.logic -> 'b List.ground = function
| Var _ -> failwith "variable list"
| Value List.Nil -> List.Nil
| Value (List.Cons (x, xs)) -> List.Cons (f x, logic_list_to_ground f xs)

let rec logic_lama_t_to_ground : logic_lama_t -> ground_lama_t = function
| Var (i, _) -> TName i
| Value x -> GT.gmap lama_t
    from_logic
    (logic_list_to_ground from_logic)
    logic_lama_c_to_ground
    (logic_list_to_ground logic_lama_t_to_ground)
    logic_lama_t_to_ground
    (logic_list_to_ground logic_sexp_to_ground)
    x

and logic_sexp_to_ground
    : (string logic * logic_lama_t List.logic) logic
    -> string * ground_lama_t List.ground
= function
| Var _ -> failwith "variable sexp variant"
| Value (x, ts) -> (from_logic x, logic_list_to_ground logic_lama_t_to_ground ts)

and logic_lama_c_to_ground : logic_lama_c -> ground_lama_c = function
| Var (_, _) -> failwith "variable constraint"
| Value x -> GT.gmap lama_c
    logic_lama_c_to_ground
    logic_nat_to_ground
    from_logic
    (logic_list_to_ground logic_lama_t_to_ground)
    logic_lama_t_to_ground
    x

(* xs[i] = x *)
let rec list_index (i : Nat.injected) (xs : 'a List.injected) (x : 'a) = ocanren
    { fresh x', xs' in xs == x' :: xs' &
        { i == 0 & x == x'
        | fresh i' in i == Nat.s i' & list_index i' xs' x
        }
    }

(* res <=> exists i. xs[i] = x *)
let rec list_member (x : 'a) (xs : 'a List.injected) (res : bool ilogic) = ocanren
    { xs == [] & res == false
    | fresh x', xs' in xs == x' :: xs' &
        { x == x' & res == true
        | x =/= x' & list_member x xs' res
        }
    }

let rec subst_v x s t = ocanren
    { s == [] & t == TName x
    | fresh x', t', s' in s == (x', t') :: s' &
        { x' == x & t == t'
        | x' =/= x & subst_v x s' t
        }
    }

let rec filter_subst xs s res = ocanren
    { s == [] & res == []
    | fresh x, t, s', has_var in s == (x, t) :: s'
        & list_member x xs has_var &
        { has_var == true & filter_subst xs s' res
        | has_var == false & fresh res' in res == (x, t) :: res'
            & filter_subst xs s' res'
        }
    }

let rec subst_t s t t' =
    (*
    debug_var t (Fun.flip reify_lama_t) (fun t ->
        debug_var t' (Fun.flip reify_lama_t) (fun t' ->
            Printf.printf "subst : %s |-> %s\n"
                (GT.show GT.list (GT.show logic_lama_t) t)
                (GT.show GT.list (GT.show logic_lama_t) t') ;
            success)) &&&
    *)
    ocanren
    { { fresh x in t == TName x & subst_v x s t' }
    | t == TInt & t' == TInt
    | t == TString & t' == TString
    | { fresh fxs, s', fc, fc', fts, fts', ft, ft' in t == TArrow (fxs, fc, fts, ft)
        & t' == TArrow (fxs, fc', fts', ft')
        & filter_subst fxs s s'
        & subst_c s' fc fc'
        & List.mapo (subst_t s') fts fts'
        & subst_t s' ft ft'
        }
    | { fresh at, at' in t == TArray at & t' == TArray at' & subst_t s at at' }
    | { fresh xs, xs' in t == TSexp xs & t' == TSexp xs' & List.mapo (subst_sexp s) xs xs' }
    }

and subst_sexp s xts xts' = ocanren
    { fresh x, ts, ts' in xts == (x, ts)
        & xts' == (x, ts')
        & List.mapo (subst_t s) ts ts'
    }

and subst_c s c c' = ocanren
    { c == CTop & c' == CTop
    | { fresh c1, c2, c1', c2' in c == CAnd (c1, c2)
        & c' == CAnd (c1', c2')
        & subst_c s c1 c1'
        & subst_c s c2 c2' }
    | { fresh t1, t2, t1', t2' in c == CEq (t1, t2)
        & c' == CEq (t1', t2')
        & subst_t s t1 t1'
        & subst_t s t2 t2' }
    | { fresh t, t' in c == CBox t & c' == CBox t' & subst_t s t t' }
    | { fresh t, t' in c == CFun t & c' == CFun t' & subst_t s t t' }
    | { fresh t1, t2, t1', t2' in c == CInd (t1, t2)
        & c' == CInd (t1', t2')
        & subst_t s t1 t1'
        & subst_t s t2 t2' }
    | { fresh i, t1, t2, t1', t2' in c == CIndI (i, t1, t2)
        & c' == CIndI (i, t1', t2')
        & subst_t s t1 t1'
        & subst_t s t2 t2' }
    | { fresh t, t' in c == CSexp t & c' == CSexp t' & subst_t s t t' }
    | { fresh x', t, ts, t', ts' in c == CSexpX (x', t, ts)
        & c' == CSexpX (x', t', ts')
        & subst_t s t t'
        & List.mapo (subst_t s) ts ts' }
    | { fresh f, ts, t, f', ts', t' in c == CCall (f, ts, t)
        & c' == CCall (f', ts', t')
        & subst_t s f f'
        & subst_t s t t'
        & List.mapo (subst_t s) ts ts' }
    }

let rec make_subst xs res = ocanren
    { xs == [] & res == []
    | fresh x, s, xs', res' in xs == x :: xs'
        & res == (x, s) :: res'
        & make_subst xs' res'
    }

let ind_sexp_hlp xs (t : injected_lama_t) : goal =
    let f' (t' : injected_lama_t) res : goal = ocanren
        { t == t' & res == true
        | t =/= t' & res == false
        } in

    let f xts res : goal = ocanren {
        fresh x, ts, ts' in xts == (x, ts)
        & List.mapo f' ts ts'
        & List.allo ts' res
    } in

    ocanren { fresh xs' in List.mapo f xs xs' & List.allo xs' true }

let ind_i_sexp_hlp (i : Nat.injected) xs (t : injected_lama_t) : goal =
    let f xts res : goal = ocanren {
        fresh x, ts, t' in xts == (x, ts) & list_index i ts t'
            & { t == t' & res == true | t =/= t' & res == false }
    } in

    ocanren { fresh xs' in List.mapo f xs xs' & List.allo xs' true }

let sexp_x_hlp (x : string ilogic) xs (ts : injected_lama_t List.injected) : goal =
    let f xts res : goal = ocanren
        { xts == (x, ts) & res == true
        | xts =/= (x, ts) & res == false
        }
    in

    ocanren { fresh xs' in List.mapo f xs xs' & List.anyo xs' true }

let rec ( //- ) (c : injected_lama_c) (c' : injected_lama_c) : goal =
    (*
    debug_var c' (Fun.flip reify_lama_c) (fun c's ->
        Printf.printf "||- %s\n" (GT.show GT.list (GT.show logic_lama_c) c's) ;
        success) &&&
    *)
    ocanren
    { c == c' (* C-Refl *)
    | c' == CTop (* C-Top *)
    | { fresh c1, c2 in c' == CAnd (c1, c2) & c //- c1 & c //- c2 } (* C-And *)
    | { fresh c1, c2 in c == CAnd (c1, c2) & c1 //- c' } (* C-AndL *)
    | { fresh c1, c2 in c == CAnd (c1, c2) & c2 //- c' } (* C-AndR *)
    (* | { fresh t1, t2 in c' == CEq (t1, t2) & t1 == t2 } *)
    | { fresh t, s in c' == CBox t & c //- CInd (t, s) } (* C-BoxInd *)
    | { fresh t in c' == CBox t & c //- CSexp t } (* C-BoxSexp *)
    | { fresh t in c' == CBox t & c //- CFun t } (* C-BoxFun *)
    | { fresh xs, c'', ts, t in c' == CFun (TArrow (xs, c'', ts, t)) } (* C-Fun *)
    | c' == CInd (TString, TInt) (* C-IndString *)
    | { fresh t in c' == CInd (TArray t, t) } (* C-IndArray *)
    | { fresh xs, t in c' == CInd (TSexp xs, t) & ind_sexp_hlp xs t } (* C-IndSexp *)
    | { fresh i, t, s in c' == CIndI (i, t, s) & c //- CInd (t, s) } (* C-IndIInd *)
    | { fresh i, xs, t in c' == CIndI (i, TSexp xs, t) & ind_i_sexp_hlp i xs t } (* C-IndISexp *)
    | { fresh xs in c' == CSexp (TSexp xs) } (* C-Sexp *)
    | { fresh x, xs, ts in c' == CSexpX (x, TSexp xs, ts) & sexp_x_hlp x xs ts } (* C-SexpX *)
    | { fresh fxs, s, fc, fc', fts, ft, ts, t in c' == CCall (TArrow (fxs, fc, fts, ft), ts, t)
        & make_subst fxs s & subst_t s ft t & subst_c s fc fc' & List.mapo (subst_t s) fts ts
        & c //- fc' } (* C-Call *)
    }


(* Continuation-passing style monad *)
module Monad = struct

    type 'a t = ('a -> goal) -> goal

    let return (x : 'a) : 'a t = fun f -> f x
    let ( >>= ) (m : 'a t) (k : 'a -> 'b t) : 'b t = fun f -> m (fun a -> k a f)

    module Syntax = struct

        let ( let* ) m k = m >>= k
    end
end

module T = Typing
module TT = T.Type
module Subst = Map.Make(Int)

let rec project_t : ground_lama_t -> TT.t = function
| TName x -> TT.Name x
| TInt -> TT.Int
| TString -> TT.String
| TArrow (xs, c, ts, t) -> TT.Arrow
    ( TT.IS.of_seq @@ OrigList.to_seq @@ List.to_list Fun.id xs
    , project_c c
    , List.to_list project_t ts
    , project_t t
    )
| TArray t -> TT.Array (project_t t)
| TSexp xs -> TT.Sexp (List.to_list (fun (x, ts) -> x, List.to_list project_t ts) xs)

and project_c : ground_lama_c -> TT.c = function
| CTop -> TT.Top
| CAnd (l, r) -> TT.And (project_c l, project_c r)
| CEq (l, r) -> TT.Eq (project_t l, project_t r)
| CBox t -> TT.Box (project_t t)
| CFun t -> TT.Fun (project_t t)
| CInd (l, r) -> TT.Ind (project_t l, project_t r)
| CIndI (i, l, r) -> TT.IndI (Nat.to_int i, project_t l, project_t r)
| CSexp t -> TT.SexpC (project_t t)
| CSexpX (x, t, ts) -> TT.SexpX (x, project_t t, List.to_list project_t ts)
| CCall (t, ss, s) -> TT.Call (project_t t, List.to_list project_t ss, project_t s)

let make_inject () =
    let module M = Monad in
    let open M.Syntax in

    let free_vars = Stdlib.ref Subst.empty in

    let rec inject_list f = function
    | [] -> M.return @@ List.nil ()
    | x :: xs ->
        let* x = f x in
        let* xs = inject_list f xs in
        M.return @@ List.cons x xs
    in

    let rec inject_t (bvs : TT.IS.t) : TT.t -> injected_lama_t M.t = function
    | TT.Name x when TT.IS.mem x bvs -> M.return @@ tName !!x
    | TT.Name x -> (match Subst.find_opt x !free_vars with
        | None -> let* fv = call_fresh in free_vars := Subst.add x fv !free_vars ; M.return fv
        | Some t -> M.return t)
    | TT.Int -> M.return @@ tInt ()
    | TT.String -> M.return @@ tString ()
    | TT.Arrow (xs, c, ts, t) ->
        let bvs = TT.IS.union bvs xs in

        let xs = List.list @@ OrigList.map (!!) @@ TT.IS.elements xs in

        let* c = inject_c bvs c in
        let* ts = inject_list (inject_t bvs) ts in
        let* t = inject_t bvs t in

        M.return @@ tArrow xs c ts t
    | TT.Array t -> let* t = inject_t bvs t in M.return @@ tArray t
    | TT.Sexp xs -> let* xs = inject_list (inject_sexp bvs) xs in M.return @@ tSexp xs

    and inject_sexp bvs (x, ts) =
        let* ts = inject_list (inject_t bvs) ts in
        M.return !!(!!x, ts)

    and inject_c (bvs : TT.IS.t) : TT.c -> injected_lama_c M.t = function
    | TT.Top -> M.return @@ cTop ()
    | TT.And (l, r) ->
        let* l = inject_c bvs l in
        let* r = inject_c bvs r in
        M.return @@ cAnd l r
    | TT.Eq (l, r) ->
        let* l = inject_t bvs l in
        let* r = inject_t bvs r in
        M.return @@ cEq l r
    | TT.Box t -> let* t = inject_t bvs t in M.return @@ cBox t
    | TT.Fun t -> let* t = inject_t bvs t in M.return @@ cFun t
    | TT.Ind (l, r) ->
        let* l = inject_t bvs l in
        let* r = inject_t bvs r in
        M.return @@ cInd l r
    | TT.IndI (i, l, r) ->
        let* l = inject_t bvs l in
        let* r = inject_t bvs r in
        M.return @@ cIndI (Nat.nat @@ Nat.of_int i) l r
    | TT.SexpC t -> let* t = inject_t bvs t in M.return @@ cSexp t
    | TT.SexpX (x, t, ts) ->
        let* t = inject_t bvs t in
        let* ts = inject_list (inject_t bvs) ts in
        M.return @@ cSexpX !!x t ts
    | TT.Call (t, ss, s) ->
        let* t = inject_t bvs t in
        let* ss = inject_list (inject_t bvs) ss in
        let* s = inject_t bvs s in
        M.return @@ cCall t ss s
    in

    object

        method free_vars = !free_vars

        method list = inject_list
        method t = inject_t
        method c = inject_c
    end

let solve (c : TT.c) : TT.t Subst.t =
    let inject = make_inject () in

    (*
    (* for debug *)

    let make_goal (ans : injected_lama_c) : goal = inject_c TT.IS.empty c (fun c ->
        let free_vars = Subst.to_seq !free_vars in

        Seq.iter (Printf.printf "%d ") @@ Seq.map fst free_vars ;
        print_endline "" ;

        ocanren { ans == c }
    ) in

    let res = run q make_goal (fun x -> x#reify reify_lama_c) in

    Stream.iter (fun res -> print_endline @@ GT.show logic_lama_c res) res ;
    *)

    let make_goal (ans : injected_lama_t List.injected) : goal = inject#c TT.IS.empty c (fun c ->
        let free_vars = Subst.to_seq inject#free_vars in

        print_string "Free variables: " ;
        Seq.iter (Printf.printf "%d ") @@ Seq.map fst free_vars ;
        print_newline () ;

        let free_vars = List.list @@ OrigList.of_seq @@ Seq.map snd free_vars in

        ocanren { CTop //- c & ans == free_vars }
    ) in

    let res = run q make_goal (fun x -> x#reify @@ List.prj_exn reify_lama_t) in

    (*
    (* too slow *)
    (* TODO fix relations and remove set *)
    let module Ans = struct

        type t = ground_lama_t list

        let compare = GT.compare GT.list (GT.compare ground_lama_t)
        let compare l r = GT.cmp_to_int @@ compare l r
    end in

    let module AS = Set.Make(Ans) in

    (*
    let ans = Stream.fold (fun ans res ->
        let ans = AS.add (List.to_list logic_lama_t_to_ground res) ans in

        if AS.cardinal ans > 1
        then failwith "more than one solution found"
        else ans
    ) AS.empty res in
    *)

    let ans = Stream.fold (fun ans res ->
        AS.add (List.to_list logic_lama_t_to_ground res) ans
    ) AS.empty res in

    let ans = AS.elements ans in

    (* type system has no most general type so we allow multiple different results *)

    let ans = match ans with
    | [] -> failwith "no one solution found"
    | [ans] -> ans
    | ans :: _ as anss ->
        Printf.printf "More than one solution found:\n" ;
        OrigList.iter print_endline
            @@ OrigList.map (GT.show GT.list (GT.show ground_lama_t)) anss ;
        ans
    in
    *)

    let ans = Stream.take ~n:1 @@ Stream.map (List.to_list logic_lama_t_to_ground) res in

    let ans = match ans with
    | [] -> failwith "no one solution found"
    | [ans] -> ans
    | _ -> failwith "not reachable"
    in

    print_endline @@ "Answer: " ^ GT.show GT.list (GT.show ground_lama_t) ans ;

    let free_vars = Seq.map fst @@ Subst.to_seq inject#free_vars in

    let subst = Seq.fold_left (fun subst (v, t) -> Subst.add v t subst) Subst.empty
        @@ Seq.zip free_vars (OrigList.to_seq ans) in

    if Subst.cardinal subst <> OrigList.length ans
    then failwith "wrong substitution size"
    else Subst.map project_t subst
