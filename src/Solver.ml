
module OrigList = List

open GT

open OCanren
open OCanren.Std


@type ('var, 'var_list, 'c, 't_list, 't, 'sexp) lama_t =
| TName of 'var
| TInt
| TString
| TArray of 't
| TSexp of 'sexp
| TArrow of 'var_list * 'c * 't_list * 't
with show, compare, foldl, gmap

@type ('t, 'p, 'p_list, 'str) lama_p =
| PWildcard
| PTyped    of 't * 'p
| PArray    of 'p_list
| PSexp     of 'str * 'p_list
| PBoxed
| PUnboxed
| PStringTag
| PArrayTag
| PSexpTag
| PFunTag
with show, compare, foldl, gmap

@type ('c, 'str, 't_list, 't, 'p_list) lama_c =
| CTop
| CAnd of 'c * 'c
| CEq of 't * 't
| CInd of 't * 't
| CCall of 't * 't_list * 't
| CMatch of 't * 'p_list
| CSexp of 'str * 't * 't_list
with show, compare, foldl, gmap

@type ground_lama_t =
    ( int
    , int List.ground
    , ground_lama_c
    , ground_lama_t List.ground
    , ground_lama_t
    , (string * ground_lama_t List.ground) List.ground
    ) lama_t
and ground_lama_p =
    ( ground_lama_t
    , ground_lama_p
    , ground_lama_p List.ground
    , string
    ) lama_p
and ground_lama_c =
    ( ground_lama_c
    , string
    , ground_lama_t List.ground
    , ground_lama_t
    , ground_lama_p List.ground
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
and logic_lama_p =
    ( logic_lama_t
    , logic_lama_p
    , logic_lama_p List.logic
    , string logic
    ) lama_p logic
and logic_lama_c =
    ( logic_lama_c
    , string logic
    , logic_lama_t List.logic
    , logic_lama_t
    , logic_lama_p List.logic
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
and injected_lama_p =
    ( injected_lama_t
    , injected_lama_p
    , injected_lama_p List.injected
    , string ilogic
    ) lama_p ilogic
and injected_lama_c =
    ( injected_lama_c
    , string ilogic
    , injected_lama_t List.injected
    , injected_lama_t
    , injected_lama_p List.injected
    ) lama_c ilogic


let tName x = OCanren.inj (TName x)
let tInt () = OCanren.inj TInt
let tString () = OCanren.inj TString
let tArray t = OCanren.inj (TArray t)
let tSexp xs = OCanren.inj (TSexp xs)
let tArrow xs c ts t = OCanren.inj (TArrow (xs, c, ts, t))

let pWildcard () = OCanren.inj PWildcard
let pTyped t p = OCanren.inj (PTyped (t, p))
let pArray ps = OCanren.inj (PArray ps)
let pSexp x ps = OCanren.inj (PSexp (x, ps))
let pBoxed () = OCanren.inj PBoxed
let pUnboxed () = OCanren.inj PUnboxed
let pStringTag () = OCanren.inj PStringTag
let pArrayTag () = OCanren.inj PArrayTag
let pSexpTag () = OCanren.inj PSexpTag
let pFunTag () = OCanren.inj PFunTag

let cTop () = OCanren.inj CTop
let cAnd c1 c2 = OCanren.inj (CAnd (c1, c2))
let cEq t1 t2 = OCanren.inj (CEq (t1, t2))
let cInd t s = OCanren.inj (CInd (t, s))
let cCall t ss s = OCanren.inj (CCall (t, ss, s))
let cMatch t ps = OCanren.inj (CMatch (t, ps))
let cSexp x t ss = OCanren.inj (CSexp (x, t, ss))

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

let reify_lama_p
    (reify_lama_t : (injected_lama_t, logic_lama_t) Reifier.t)
    : (injected_lama_p, logic_lama_p) Reifier.t =
    let open Env.Monad in
    let open Syntax in

    let* reify_string = Reifier.reify in
    let* reify_lama_t = reify_lama_t in

    Reifier.fix (fun self ->
        let* reify_lama_p_list = List.reify self in
        let* self = self in

        Reifier.compose Reifier.reify (
            let rec f = function
            | Var (i, xs) -> Var (i, Stdlib.List.map f xs)
            | Value x -> Value (GT.gmap lama_p
                reify_lama_t
                self
                reify_lama_p_list
                reify_string
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

    let* reify_string = Reifier.reify in
    let* reify_lama_p_list = List.reify (reify_lama_p reify_lama_t) in
    let* reify_lama_t_list = List.reify reify_lama_t in
    let* reify_lama_t = reify_lama_t in

    Reifier.fix (fun self ->
        let* self = self in

        Reifier.compose Reifier.reify (
            let rec f = function
            | Var (i, xs) -> Var (i, Stdlib.List.map f xs)
            | Value x -> Value (GT.gmap lama_c
                self
                reify_string
                reify_lama_t_list
                reify_lama_t
                reify_lama_p_list
                x)
            in

            return f
        )
    )

let reify_lama_t = reify_lama_t reify_lama_c
let reify_lama_p = reify_lama_p reify_lama_t
let reify_lama_c = reify_lama_c reify_lama_t

let rec logic_list_to_ground (f : 'a -> 'b) : 'a List.logic -> 'b List.ground = function
| Var _ -> List.Nil
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

and logic_lama_p_to_ground : logic_lama_p -> ground_lama_p = function
| Var _ -> failwith "variable type pattern"
| Value x -> GT.gmap lama_p
    logic_lama_t_to_ground
    logic_lama_p_to_ground
    (logic_list_to_ground logic_lama_p_to_ground)
    from_logic
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
    from_logic
    (logic_list_to_ground logic_lama_t_to_ground)
    logic_lama_t_to_ground
    (logic_list_to_ground logic_lama_p_to_ground)
    x

(* res <=> exists i. xs[i] = x *)
let rec list_member (x : 'a) (xs : 'a List.injected) (res : bool ilogic) = ocanren
    { xs == [] & res == false
    | fresh x', xs' in xs == x' :: xs' &
        { res == true & x == x'
        | x =/= x' & list_member x xs' res
        }
    }

(* partition list [(k, v)] on [v] and [(k', v)], k =/= k' *)
let rec partition k kvs vs1 kvs2 = ocanren
    { kvs == [] & vs1 == [] & kvs2 == []
    | fresh k', v, kvs' in kvs == (k', v) :: kvs' &
        { k == k' & { fresh vs1' in vs1 == v :: vs1' & partition k kvs' vs1' kvs2 }
        | k =/= k' & { fresh kvs2' in kvs2 == (k', v) :: kvs2' & partition k kvs' vs1 kvs2' }
        }
    }

(* [(k, v)] -> [(k, [v])], k distinct *)
let rec group_by_fst kvs res = ocanren
    { kvs == [] & res == []
    | fresh k, v, vs, kvs', kvs'', res' in kvs == (k, v) :: kvs'
        & res == (k, vs) :: res' & partition k kvs vs kvs''
        & group_by_fst kvs'' res'
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
    | { fresh at, at' in t == TArray at & t' == TArray at' & subst_t s at at' }
    | { fresh xs, xs' in t == TSexp xs & t' == TSexp xs' & List.mapo (subst_sexp s) xs xs' }
    | { fresh fxs, s', fc, fc', fts, fts', ft, ft' in t == TArrow (fxs, fc, fts, ft)
        & t' == TArrow (fxs, fc', fts', ft')
        & filter_subst fxs s s'
        & subst_c s' fc fc'
        & List.mapo (subst_t s') fts fts'
        & subst_t s' ft ft'
        }
    }

and subst_sexp s xts xts' = ocanren
    { fresh x, ts, ts' in xts == (x, ts)
        & xts' == (x, ts')
        & List.mapo (subst_t s) ts ts'
    }

and subst_p s p p' = ocanren
    { p == PWildcard & p' == PWildcard
    | { fresh t, p1, t', p1' in p == PTyped (t, p1) & p' == PTyped (t', p1')
        & subst_t s t t' & subst_p s p1 p1' }
    | { fresh ps, ps' in p == PArray ps & p' == PArray ps' & List.mapo (subst_p s) ps ps' }
    | { fresh x, ps, ps' in p == PSexp (x, ps) & p' == PSexp (x, ps')
        & List.mapo (subst_p s) ps ps' }
    | p == PBoxed & p' == PBoxed
    | p == PUnboxed & p' == PUnboxed
    | p == PStringTag & p' == PStringTag
    | p == PArrayTag & p' == PArrayTag
    | p == PSexpTag & p' == PSexpTag
    | p == PFunTag & p' == PFunTag
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
    | { fresh t1, t2, t1', t2' in c == CInd (t1, t2)
        & c' == CInd (t1', t2')
        & subst_t s t1 t1'
        & subst_t s t2 t2' }
    | { fresh f, ts, t, f', ts', t' in c == CCall (f, ts, t)
        & c' == CCall (f', ts', t')
        & subst_t s f f'
        & subst_t s t t'
        & List.mapo (subst_t s) ts ts' }
    | { fresh t, ps, t', ps' in c == CMatch (t, ps)
        & c' == CMatch (t', ps')
        & subst_t s t t'
        & List.mapo (subst_p s) ps ps' }
    | { fresh x', t, ts, t', ts' in c == CSexp (x', t, ts)
        & c' == CSexp (x', t', ts')
        & subst_t s t t'
        & List.mapo (subst_t s) ts ts' }
    }

let rec make_subst xs res = ocanren
    { xs == [] & res == []
    | fresh x, s, xs', res' in xs == x :: xs'
        & res == (x, s) :: res'
        & make_subst xs' res'
    }

type match_t_res =
    ( (injected_lama_t, injected_lama_p) Pair.injected List.injected
    , (injected_lama_t, injected_lama_t) Pair.injected List.injected
    ) Pair.injected

let rec match_t t p (res : match_t_res Option.groundi) =
    let some = Option.some in
    let none = Option.none in

    let rec array_hlp t ps res = ocanren
        { ps == [] & res == []
        | fresh p, ps', res' in ps == p :: ps' & res == (t, p) :: res' & array_hlp t ps' res'
        }
    in

    let rec sexp_hlp ts ps res = ocanren
        { ps == [] &
            { ts == [] & res == Some []
            | ts =/= [] & res == None
            }
        | fresh p, ps', t, ts', res', tps in ps == p :: ps' &
            { ts == [] & res == None
            | ts == t :: ts' & sexp_hlp ts' ps' res' &
                { res' == None & res == None
                | res' == Some tps & res == Some ((t, p) :: tps)
                }
            }
        }
    in

    (*
    debug_var t (Fun.flip reify_lama_t) (fun ts ->
        debug_var p (Fun.flip reify_lama_p) (fun ps ->
            Printf.printf "matchT(%s, %s)"
                (GT.show GT.list (GT.show logic_lama_t) ts)
                (GT.show GT.list (GT.show logic_lama_p) ps)
                ;
            print_newline () ;
            success)) &&&
    *)

    (* FIXME no =/= with fresh unbound variables *)

    ocanren
    { p == PWildcard & res == some ([], []) (* MT-Wildcard *)
    | { fresh s, p', res' in p == PTyped s p' & match_t t p' res' &
        { res' == None & res == None
        | fresh ps, eqs in res' == some (ps, eqs) & res == some (ps, (t, s) :: eqs)
        } } (* MT-Typed *)
    | { fresh t', ps, ps' in p == PArray ps &
        { t == TArray t' & res == some (ps', []) & array_hlp t' ps ps'
        | t =/= TArray t' & res == None
        } } (* MT-Array *)
    | { fresh x, ps, ts, res', tps in p == PSexp (x, ps) &
        { t == TSexp [(x, ts)] & sexp_hlp ts ps res' &
            { res' == None & res == None
            | res' == Some tps & res == some (tps, [])
            }
        | t =/= TSexp [(x, ts)] & res == None
        } } (* MT-Sexp *)
    | p == PBoxed &
        { t == TString & res == some ([], [])
        | t =/= TString & res == None
        } (* MT-BoxString *)
    | { fresh t' in p == PBoxed &
        { t == TArray t' & res == some ([], [])
        | t =/= TArray t' & res == None
        } } (* MT-BoxArray *)
    | { fresh xts in p == PBoxed &
        { t == TSexp [xts] & res == some ([], [])
        | t =/= TSexp [xts] & res == None
        } } (* MT-BoxSexp *)
    | { fresh fxs, fc, fts, ft in p == PBoxed &
        { t == TArrow (fxs, fc, fts, ft) & res == some ([], [])
        | t =/= TArrow (fxs, fc, fts, ft) & res == None
        } } (* MT-BoxArrow *)
    | p == PUnboxed &
        { t == TInt & res == some ([], [])
        | t =/= TInt & res == None
        } (* MT-IntShape *)
    | p == PStringTag &
        { t == TString & res == some ([], [])
        | t =/= TString & res == None
        } (* MT-StringShape *)
    | { fresh t' in p == PArrayTag &
        { t == TArray t' & res == some ([], [])
        | t =/= TArray t' & res == None
        } } (* MT-ArrayShape *)
    | { fresh xts in p == PSexpTag &
        { t == TSexp [xts] & res == some ([], [])
        | t =/= TSexp [xts] & res == None
        } } (* MT-SexpShape *)
    | { fresh fxs, fc, fts, ft in p == PFunTag &
        { t == TArrow (fxs, fc, fts, ft) & res == some ([], [])
        | t =/= TArrow (fxs, fc, fts, ft) & res == None
        } } (* MT-FunShape *)
    }

let ind_sexp_hlp xs (t : injected_lama_t) : goal =
    let f' (t' : injected_lama_t) res : goal = ocanren
        { res == true & t == t'
        | res == false & t =/= t'
        } in

    let f xts res : goal = ocanren {
        fresh x, ts, ts' in xts == (x, ts)
        & List.mapo f' ts ts'
        & List.allo ts' res
    } in

    ocanren { fresh xs' in List.mapo f xs xs' & List.allo xs' true }

let sexp_x_hlp (x : string ilogic) xs (ts : injected_lama_t List.injected) : goal =
    (* straightforward solution don't work here *)

    (*
    let f n xts res = ocanren {
        fresh x', ts', n' in xts == (x', ts') & List.lengtho ts' n' &
            { res == false & { x =/= x' | n =/= n' }
            | res == true & x == x' & n == n'
            }
    } in

    let g xts res = ocanren
        { res == false & xts =/= (x, ts)
        | res == true & xts == (x, ts)
        }
    in

    ocanren {
        fresh n, xs', xs'' in xs' =/= [] & List.allo xs'' true & List.lengtho ts n
            & List.filtero (f n) xs xs' & List.mapo g xs' xs''
    }
    *)

    let f n xts res = ocanren {
        fresh x', ts', n' in xts == (x', ts') & List.lengtho ts' n' &
            { res == true & { x =/= x' | n =/= n' }
            | res == false & x == x' & n == n'
            }
    } in

    let f n xs = ocanren { fresh xs' in List.mapo (f n) xs xs' & List.allo xs' true } in

    (* loops forever *)

    (*
    let initial_xs = xs in

    let rec g n xs =
        debug_var initial_xs (Fun.flip @@ List.reify @@ Pair.reify Reifier.reify (List.reify reify_lama_t)) (function
        | [xs] ->
            print_string "xs = " ;
            print_endline @@ GT.show List.logic (GT.show Pair.logic
                (GT.show logic @@ GT.show GT.string)
                (GT.show List.logic @@ GT.show logic_lama_t)) xs ;
            success
        ) &&&
        ocanren {
        fresh x', ts', xs' in xs == (x', ts') :: xs' &
            { x == x' & ts == ts' & f n xs' (* found => check no any such in tail *)
            | x =/= x' & g n xs'            (* wrong label => go next *)
            | x == x' & fresh n' in List.lengtho ts' n' (* right label => check amount of args *)
                & n =/= n' & g n xs'        (* wrong amount => go next *)
            }
        }
    in
    *)

    (* FIXME will not work *)
    let rec g n xs =
        debug_var xs (Fun.flip @@ List.reify @@ Pair.reify Reifier.reify (List.reify reify_lama_t)) (function
        | [Var _] -> ocanren { fresh xs' in xs == (x, ts) :: xs' }
        | [Value _] -> ocanren {
            fresh x', ts', xs' in xs == (x', ts') :: xs' &
                { x == x' & ts == ts' & f n xs' (* found => check no any such in tail *)
                | x =/= x' & g n xs'            (* wrong label => go next *)
                | x == x' & fresh n' in List.lengtho ts' n' (* right label => check amount of args *)
                    & n =/= n' & g n xs'        (* wrong amount => go next *)
                }
        })
    in

    ocanren { fresh n in List.lengtho ts n & g n xs }

let rec ( //- ) (c : injected_lama_c) (c' : injected_lama_c) : goal =
    (*
    debug_var c' (Fun.flip reify_lama_c) (fun c's ->
        Printf.printf "||- %s" (GT.show GT.list (GT.show logic_lama_c) c's) ;
        print_newline () ;
        success) &&&
    *)
    ocanren
    { c == c' (* C-Refl *)
    | c' == CTop (* C-Top *)
    | { fresh c1, c2 in c' == CAnd (c1, c2) & c //- c1 & c //- c2 } (* C-And *)
    | { fresh c1, c2 in c == CAnd (c1, c2) & c1 //- c' } (* C-AndL *)
    | { fresh c1, c2 in c == CAnd (c1, c2) & c2 //- c' } (* C-AndR *)
    (* | { fresh t1, t2 in c' == CEq (t1, t2) & t1 == t2 } *)
    | c' == CInd (TString, TInt) (* C-IndString *)
    | { fresh t in c' == CInd (TArray t, t) } (* C-IndArray *)
    | { fresh xs, t in c' == CInd (TSexp xs, t) & ind_sexp_hlp xs t } (* C-IndSexp *)
    | { fresh fxs, s, fc, fc', fts, ft, ts, t in c' == CCall (TArrow (fxs, fc, fts, ft), ts, t)
        & make_subst fxs s & subst_t s ft t & subst_c s fc fc' & List.mapo (subst_t s) fts ts
        & c //- fc' } (* C-Call *)
    | { fresh ps in c' == CMatch (TInt, ps) & match_t_ast c TInt ps } (* C-MatchInt *)
    | { fresh ps in c' == CMatch (TString, ps) & match_t_ast c TString ps } (* C-MatchString *)
    | { fresh t, ps in c' == CMatch (TArray t, ps) & match_t_ast c (TArray t) ps } (* C-MatchArray *)
    | { fresh xs, ps in c' == CMatch (TSexp xs, ps) & match_sexp_hlp c xs ps } (* C-MatchSexp *)
    | { fresh fxs, fc, fts, ft, ps in c' == CMatch (TArrow (fxs, fc, fts, ft), ps)
        & match_t_ast c (TArrow (fxs, fc, fts, ft)) ps } (* C-MatchFun *)
    | { fresh x, xs, ts in c' == CSexp (x, TSexp xs, ts) & sexp_x_hlp x xs ts } (* C-Sexp *)
    }

and match_sexp_hlp c xs ps = ocanren
    { xs == []
    | fresh xts, xs' in xs == xts :: xs'
        & match_t_ast c (TSexp [xts]) ps
        & match_sexp_hlp c xs' ps
    }

and match_t_ast c t ps =
    let some = Option.some in
    let none = Option.none in
    let o () = Nat.o in
    let s = Nat.s in

    let rec eqs_hlp eqs = ocanren
        { eqs == []
        | fresh t1, t2, eqs' in eqs == (t1, t2) :: eqs' & t1 == t2 & eqs_hlp eqs'
        }
    in

    let rec match_hlp ps num tps = ocanren
        { ps == [] & num == O & tps == []
        | fresh p, ps', res in ps == p :: ps' & match_t t p res &
            { res == None & match_hlp ps' num tps
            | fresh tps', tps'', num', eqs in res == some (tps', eqs)
                & num == S num' & eqs_hlp eqs & List.appendo tps' tps'' tps
                & match_hlp ps' num' tps''
            }
        }
    in

    let rec match_c_hlp tps = ocanren
        { tps == []
        | fresh t, ps, tps' in tps == (t, ps) :: tps' & c //- CMatch (t, ps) & match_c_hlp tps'
        }
    in

    (*
    debug_var c (Fun.flip reify_lama_c) (fun cs ->
        debug_var t (Fun.flip reify_lama_t) (fun ts ->
            debug_var ps (Fun.flip (List.reify reify_lama_p)) (fun pss ->
                Printf.printf "%s |- matchT*(%s, %s)"
                    (GT.show GT.list (GT.show logic_lama_c) cs)
                    (GT.show GT.list (GT.show logic_lama_t) ts)
                    (GT.show GT.list (GT.show List.logic (GT.show logic_lama_p)) pss)
                    ;
                print_newline () ;
                success))) &&&
    *)

    ocanren { fresh num, tps, tps' in match_hlp ps num tps & num =/= O
        & group_by_fst tps tps' & match_c_hlp tps' } (* MT-Ast *)


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
| TName x -> `Name x
| TInt -> `Int
| TString -> `String
| TArrow (xs, c, ts, t) -> `Arrow
    ( TT.IS.of_seq @@ OrigList.to_seq @@ List.to_list Fun.id xs
    , project_c c
    , List.to_list project_t ts
    , project_t t
    )
| TArray t -> `Array (project_t t)
| TSexp xs -> `Sexp (List.to_list (fun (x, ts) -> x, List.to_list project_t ts) xs)

and project_p : ground_lama_p -> TT.p = function
| PWildcard -> `Wildcard
| PTyped (t, p) -> `Typed (project_t t, project_p p)
| PArray ps -> `Array (List.to_list project_p ps)
| PSexp (x, ps) -> `Sexp (x, List.to_list project_p ps)
| PBoxed -> `Boxed
| PUnboxed -> `Unboxed
| PStringTag -> `StringTag
| PArrayTag -> `ArrayTag
| PSexpTag -> `SexpTag
| PFunTag -> `FunTag

and project_c : ground_lama_c -> TT.c = function
| CTop -> `Top
| CAnd (l, r) -> `And (project_c l, project_c r)
| CEq (l, r) -> `Eq (project_t l, project_t r)
| CInd (l, r) -> `Ind (project_t l, project_t r)
| CCall (t, ss, s) -> `Call (project_t t, List.to_list project_t ss, project_t s)
| CMatch (t, ps) -> `Match (project_t t, List.to_list project_p ps)
| CSexp (x, t, ts) -> `Sexp (x, project_t t, List.to_list project_t ts)

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
    | `Name x when TT.IS.mem x bvs -> M.return @@ tName !!x
    | `Name x -> (match Subst.find_opt x !free_vars with
        | None -> let* fv = call_fresh in free_vars := Subst.add x fv !free_vars ; M.return fv
        | Some t -> M.return t)
    | `Int -> M.return @@ tInt ()
    | `String -> M.return @@ tString ()
    | `Arrow (xs, c, ts, t) ->
        let bvs = TT.IS.union bvs xs in

        let xs = List.list @@ OrigList.map (!!) @@ TT.IS.elements xs in

        let* c = inject_c bvs c in
        let* ts = inject_list (inject_t bvs) ts in
        let* t = inject_t bvs t in

        M.return @@ tArrow xs c ts t
    | `Array t -> let* t = inject_t bvs t in M.return @@ tArray t
    | `Sexp xs -> let* xs = inject_list (inject_sexp bvs) xs in M.return @@ tSexp xs

    and inject_p (bvs : TT.IS.t) : TT.p -> injected_lama_p M.t = function
    | `Wildcard -> M.return @@ pWildcard ()
    | `Typed (t, p) ->
        let* t = inject_t bvs t in
        let* p = inject_p bvs p in
        M.return @@ pTyped t p
    | `Array ps ->
        let* ps = inject_list (inject_p bvs) ps in
        M.return @@ pArray ps
    | `Sexp (x, ps) ->
        let* ps = inject_list (inject_p bvs) ps in
        M.return @@ pSexp !!x ps
    | `Boxed -> M.return @@ pBoxed ()
    | `Unboxed -> M.return @@ pUnboxed ()
    | `StringTag -> M.return @@ pStringTag ()
    | `ArrayTag -> M.return @@ pArrayTag ()
    | `SexpTag -> M.return @@ pSexpTag ()
    | `FunTag -> M.return @@ pFunTag ()

    and inject_sexp bvs (x, ts) =
        let* ts = inject_list (inject_t bvs) ts in
        M.return !!(!!x, ts)

    and inject_c (bvs : TT.IS.t) : TT.c -> injected_lama_c M.t = function
    | `Top -> M.return @@ cTop ()
    | `And (l, r) ->
        let* l = inject_c bvs l in
        let* r = inject_c bvs r in
        M.return @@ cAnd l r
    | `Eq (l, r) ->
        let* l = inject_t bvs l in
        let* r = inject_t bvs r in
        M.return @@ cEq l r
    | `Ind (l, r) ->
        let* l = inject_t bvs l in
        let* r = inject_t bvs r in
        M.return @@ cInd l r
    | `Call (t, ss, s) ->
        let* t = inject_t bvs t in
        let* ss = inject_list (inject_t bvs) ss in
        let* s = inject_t bvs s in
        M.return @@ cCall t ss s
    | `Match (t, ps) ->
        let* t = inject_t bvs t in
        let* ps = inject_list (inject_p bvs) ps in
        M.return @@ cMatch t ps
    | `Sexp (x, t, ts) ->
        let* t = inject_t bvs t in
        let* ts = inject_list (inject_t bvs) ts in
        M.return @@ cSexp !!x t ts
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
