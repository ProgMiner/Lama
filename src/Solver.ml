
module OrigList = List

open GT

open OCanren
open OCanren.Std


@type ('nat, 'c_list, 't_list, 't, 'sexp) lama_t =
| TName of 'nat
| TInt
| TString
| TArray of 't
| TSexp of 'sexp
| TArrow of 'nat * 'c_list * 't_list * 't
| TMu of 't
with show, compare, foldl, gmap

@type ('t, 'p, 'p_list, 'i) lama_p =
| PWildcard
| PTyped    of 't * 'p
| PArray    of 'p_list
| PSexp     of 'i * 'p_list
| PBoxed
| PUnboxed
| PStringTag
| PArrayTag
| PSexpTag
| PFunTag
with show, compare, foldl, gmap

@type ('i, 't_list, 't, 'p_list) lama_c =
| CEq of 't * 't
| CInd of 't * 't
| CCall of 't * 't_list * 't
| CMatch of 't * 'p_list
| CSexp of 'i * 't * 't_list
with show, compare, foldl, gmap

@type ground_lama_t =
    ( Nat.ground
    , ground_lama_c List.ground
    , ground_lama_t List.ground
    , ground_lama_t
    , (int * ground_lama_t List.ground) List.ground
    ) lama_t
and ground_lama_p =
    ( ground_lama_t
    , ground_lama_p
    , ground_lama_p List.ground
    , int
    ) lama_p
and ground_lama_c =
    ( int
    , ground_lama_t List.ground
    , ground_lama_t
    , ground_lama_p List.ground
    ) lama_c
with show, compare, foldl, gmap

@type logic_lama_t =
    ( Nat.logic
    , logic_lama_c List.logic
    , logic_lama_t List.logic
    , logic_lama_t
    , (int logic * logic_lama_t List.logic) logic List.logic
    ) lama_t logic
and logic_lama_p =
    ( logic_lama_t
    , logic_lama_p
    , logic_lama_p List.logic
    , int logic
    ) lama_p logic
and logic_lama_c =
    ( int logic
    , logic_lama_t List.logic
    , logic_lama_t
    , logic_lama_p List.logic
    ) lama_c logic
with show, compare, foldl, gmap

type injected_lama_t =
    ( Nat.injected
    , injected_lama_c List.injected
    , injected_lama_t List.injected
    , injected_lama_t
    , (int ilogic * injected_lama_t List.injected) ilogic List.injected
    ) lama_t ilogic
and injected_lama_p =
    ( injected_lama_t
    , injected_lama_p
    , injected_lama_p List.injected
    , int ilogic
    ) lama_p ilogic
and injected_lama_c =
    ( int ilogic
    , injected_lama_t List.injected
    , injected_lama_t
    , injected_lama_p List.injected
    ) lama_c ilogic


let tName x = inj (TName x)
let tInt () = inj TInt
let tString () = inj TString
let tArray t = inj (TArray t)
let tSexp xs = inj (TSexp xs)
let tArrow n c ts t = inj (TArrow (n, c, ts, t))
let tMu t = inj (TMu t)

let pWildcard () = inj PWildcard
let pTyped t p = inj (PTyped (t, p))
let pArray ps = inj (PArray ps)
let pSexp x ps = inj (PSexp (x, ps))
let pBoxed () = inj PBoxed
let pUnboxed () = inj PUnboxed
let pStringTag () = inj PStringTag
let pArrayTag () = inj PArrayTag
let pSexpTag () = inj PSexpTag
let pFunTag () = inj PFunTag

let cEq t1 t2 = inj (CEq (t1, t2))
let cInd t s = inj (CInd (t, s))
let cCall t ss s = inj (CCall (t, ss, s))
let cMatch t ps = inj (CMatch (t, ps))
let cSexp x t ss = inj (CSexp (x, t, ss))

let reify_lama_t
    (reify_lama_c : (injected_lama_t, logic_lama_t) Reifier.t
                  -> (injected_lama_c, logic_lama_c) Reifier.t)
    : (injected_lama_t, logic_lama_t) Reifier.t =
    let open Env.Monad in
    let open Syntax in

    let* reify_string = Reifier.reify in
    let* reify_nat = Nat.reify in

    Reifier.fix (fun self ->
        let* reify_lama_c_list = List.reify @@ reify_lama_c self in
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
                reify_nat
                reify_lama_c_list
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

    Reifier.compose Reifier.reify (
        let rec f = function
        | Var (i, xs) -> Var (i, Stdlib.List.map f xs)
        | Value x -> Value (GT.gmap lama_c
            reify_string
            reify_lama_t_list
            reify_lama_t
            reify_lama_p_list
            x)
        in

        return f
    )

let reify_lama_t = reify_lama_t reify_lama_c
let reify_lama_p = reify_lama_p reify_lama_t
let reify_lama_c = reify_lama_c reify_lama_t

let reify_subst xs = List.reify (Pair.reify Nat.reify reify_lama_t) xs
let show_subst = GT.show List.logic @@ GT.show Pair.logic
    (GT.show Nat.logic) (GT.show logic_lama_t)

let rec logic_nat_to_ground : Nat.logic -> Nat.ground = function
| Var _ -> failwith "variable nat"
| Value Nat.O -> Nat.O
| Value (Nat.S n) -> Nat.S (logic_nat_to_ground n)

let rec logic_list_to_ground (f : 'a -> 'b) : 'a List.logic -> 'b List.ground = function
| Var _ -> []
| Value List.Nil -> []
| Value (List.Cons (x, xs)) -> f x :: logic_list_to_ground f xs

let rec logic_lama_t_to_ground : logic_lama_t -> ground_lama_t = function
| Var _ -> print_endline "oaoaoa" ; failwith "variable type"
| Value x -> GT.gmap lama_t
    logic_nat_to_ground
    (logic_list_to_ground logic_lama_c_to_ground)
    (logic_list_to_ground logic_lama_t_to_ground)
    logic_lama_t_to_ground
    (logic_list_to_ground logic_sexp_to_ground)
    x

and logic_sexp_to_ground
    : (int logic * logic_lama_t List.logic) logic
    -> int * ground_lama_t List.ground
= function
| Var _ -> failwith "variable sexp variant"
| Value (x, ts) -> (from_logic x, logic_list_to_ground logic_lama_t_to_ground ts)

and logic_lama_p_to_ground : logic_lama_p -> ground_lama_p = function
| Var _ -> failwith "variable type pattern"
| Value x -> GT.gmap lama_p
    logic_lama_t_to_ground
    logic_lama_p_to_ground
    (logic_list_to_ground logic_lama_p_to_ground)
    from_logic
    x

and logic_lama_c_to_ground : logic_lama_c -> ground_lama_c = function
| Var (_, _) -> failwith "variable constraint"
| Value x -> GT.gmap lama_c
    from_logic
    (logic_list_to_ground logic_lama_t_to_ground)
    logic_lama_t_to_ground
    (logic_list_to_ground logic_lama_p_to_ground)
    x

let logic_to_injected (vars : term_vars) = function
| Var (v, _) -> vars.get v
| Value x -> inj x

let rec logic_nat_to_injected (vars : term_vars) = function
| Var (v, _) -> vars.get v
| Value x -> inj @@ GT.gmap Nat.t (logic_nat_to_injected vars) x

let rec logic_list_to_injected (vars : term_vars) (f : 'a -> 'b)
    : 'a List.logic -> 'b List.injected = function
| Var (v, _) -> vars.get v
| Value x -> inj @@ GT.gmap List.t f (logic_list_to_injected vars f) x

let rec logic_lama_t_to_injected (vars : term_vars) : logic_lama_t -> injected_lama_t = function
| Var (v, _) -> vars.get v
| Value x -> inj @@ GT.gmap lama_t
    (logic_nat_to_injected vars)
    (logic_list_to_injected vars @@ logic_lama_c_to_injected vars)
    (logic_list_to_injected vars @@ logic_lama_t_to_injected vars)
    (logic_lama_t_to_injected vars)
    (logic_list_to_injected vars @@ logic_sexp_to_injected vars)
    x

and logic_sexp_to_injected (vars : term_vars)
    : (int logic * logic_lama_t List.logic) logic
    -> (int ilogic * injected_lama_t List.injected) ilogic
= function
| Var (v, _) -> vars.get v
| Value (x, ts) -> inj ( logic_to_injected vars x
                       , logic_list_to_injected vars (logic_lama_t_to_injected vars) ts
                       )

and logic_lama_p_to_injected (vars : term_vars) : logic_lama_p -> injected_lama_p = function
| Var (v, _) -> vars.get v
| Value x -> inj @@ GT.gmap lama_p
    (logic_lama_t_to_injected vars)
    (logic_lama_p_to_injected vars)
    (logic_list_to_injected vars @@ logic_lama_p_to_injected vars)
    (logic_to_injected vars)
    x

and logic_lama_c_to_injected (vars : term_vars) : logic_lama_c -> injected_lama_c = function
| Var (v, _) -> vars.get v
| Value x -> inj @@ GT.gmap lama_c
    (logic_to_injected vars)
    (logic_list_to_injected vars @@ logic_lama_t_to_injected vars)
    (logic_lama_t_to_injected vars)
    (logic_list_to_injected vars @@ logic_lama_p_to_injected vars)
    x

let rec lift_var min : int -> Nat.logic -> Nat.logic =
    if min < 0 then invalid_arg "minimum must not be negative" ;

    let rec incr add x =
        if add < 0 then invalid_arg "addend must not be negative" ;
        if add = 0 then x else incr (add - 1) @@ Value (Nat.S x)
    in

    if min = 0 then incr else fun add -> function
        | Var _ -> failwith "unable to lift variable natural"
        | Value Nat.O -> Value Nat.O
        | Value (Nat.S n) -> lift_var (min - 1) (add + 1) n

let rec lift_vars_t min add : logic_lama_t -> logic_lama_t = GT.gmap logic @@ function
    | TName n -> TName (lift_var min add n)
    | TInt -> TInt
    | TString -> TString
    | TArray t -> TArray (lift_vars_t min add t)
    | TSexp xs -> TSexp (GT.gmap List.logic (GT.gmap Pair.logic Fun.id
        @@ GT.gmap List.logic @@ lift_vars_t min add) xs)

    | TArrow (n, c, ts, t) ->
        let n' = Nat.to_int @@ logic_nat_to_ground n in
        let min = min + n' in

        TArrow (n, GT.gmap List.logic (lift_vars_c min add) c,
            GT.gmap List.logic (lift_vars_t min add) ts, lift_vars_t min add t)

    | TMu t -> TMu (lift_vars_t (min + 1) add t)

and lift_vars_p min add = GT.gmap logic @@ GT.gmap lama_p (lift_vars_t min add)
    (lift_vars_p min add) (GT.gmap List.logic @@ lift_vars_p min add) Fun.id

and lift_vars_c min add = GT.gmap logic @@ GT.gmap lama_c Fun.id
    (GT.gmap List.logic @@ lift_vars_t min add) (lift_vars_t min add)
    (GT.gmap List.logic @@ lift_vars_p min add)

let occurs_hook_lama_t vars v t =
    let get_var u = if v = u then Obj.magic @@ tName Nat.O else vars.get u in
    tMu @@ logic_lama_t_to_injected { get = get_var } @@ lift_vars_t 0 1 t

let set_occurs_hook_lama_t t = bind_occurs_hook t reify_lama_t occurs_hook_lama_t

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

(* x = min_lt(xs), xs' = xs \ x *)
let list_minimum lt =
    let rec hlp xs x xs' = ocanren
        { xs == [x] & xs' == []
        | fresh x1, xs1, x1', xs1', res in xs == x1 :: xs1 & hlp xs1 x1' xs1' & lt x1 x1' res &
            { res == true & x == x1 & xs' == xs1
            | res == false & x == x1' & xs' == x1 :: xs1'
            }
        }
    in

    hlp

let rec eq_list eq xs xs' = ocanren
    { xs == xs'
    | xs =/= xs' &
        { is_var xs & is_var     xs' & xs == xs'
        | is_var xs & is_not_var xs' &
            { xs' == [] & xs == xs'
            | fresh x, x', xs1, xs1' in xs' == x' :: xs1' & xs == x :: xs1
                & eq x x' & eq_list eq xs1 xs1'
            }
        | is_not_var xs &
            { xs == [] & xs == xs'
            | fresh x, x', xs1, xs1' in xs == x :: xs1 & xs' == x' :: xs1'
                & eq x x' & eq_list eq xs1 xs1'
            }
        }
    }

let rec eq_t t t' = ocanren
    { t == t'
    | t =/= t' &
        { is_var     t & is_var     t' & t == t'
        | is_var     t & is_not_var t' & set_occurs_hook_lama_t t  & t == t'
        | is_not_var t & is_var     t' & set_occurs_hook_lama_t t' & t == t'
        | is_not_var t & is_not_var t' &
            { t == TName _ & t == t'
            | t == TInt    & t == t'
            | t == TString & t == t'
            | { fresh t1, t1' in t == TArray t1 & t' == TArray t1' & eq_t t1 t1' }
            | { fresh xs, xs' in t == TSexp xs & t' == TSexp xs' & eq_sexp_hlp xs xs' }
            | { fresh n, c, c', ts, ts', t1, t1' in t == TArrow (n, c, ts, t1)
                & t' == TArrow (n, c', ts', t1') & eq_list eq_c c c'
                & eq_t_list ts ts' & eq_t t1 t' }
            | { fresh t1, t1' in t == TMu t1 & t' == TMu t1' & eq_t t1 t1' }
            }
        }
    }

and eq_sexp_hlp =
    let hlp xts xts' = ocanren {
        fresh x, ts, ts' in xts == (x, ts) & xts' == (x, ts') & eq_t_list ts ts'
    } in

    fun xs xs' -> eq_list hlp xs xs'

and eq_t_list ts ts' = eq_list eq_t ts ts'

and eq_p p p' = ocanren
    { p == p'
    | p =/= p' &
        { is_var p & is_var p' & p == p'
        | is_var p & is_not_var p' &
            { p' == PWildcard & p == p'
            | { fresh t, t', p1, p1' in p' == PTyped (t', p1') & p == PTyped (t, p1)
                & eq_t t t' & eq_p p1 p1' }
            | { fresh ps, ps' in p' == PArray ps' & p == PArray ps & eq_list eq_p ps ps' }
            | { fresh x, ps, ps' in p' == PSexp (x, ps') & p == PSexp (x, ps) & eq_list eq_p ps ps' }
            | p' == PBoxed & p == p'
            | p' == PUnboxed & p == p'
            | p' == PStringTag & p == p'
            | p' == PArrayTag & p == p'
            | p' == PSexpTag & p == p'
            | p' == PFunTag & p == p'
            }
        | is_not_var p &
            { p == PWildcard & p == p'
            | { fresh t, t', p1, p1' in p == PTyped (t, p1) & p' == PTyped (t', p1')
                & eq_t t t' & eq_p p1 p1' }
            | { fresh ps, ps' in p == PArray ps & p' == PArray ps' & eq_list eq_p ps ps' }
            | { fresh x, ps, ps' in p == PSexp (x, ps) & p' == PSexp (x, ps') & eq_list eq_p ps ps' }
            | p == PBoxed & p == p'
            | p == PUnboxed & p == p'
            | p == PStringTag & p == p'
            | p == PArrayTag & p == p'
            | p == PSexpTag & p == p'
            | p == PFunTag & p == p'
            }
        }
    }

and eq_c c c' = ocanren
    { c == c'
    | c =/= c' &
        { is_var c & is_var     c' & c == c'
        | is_var c & is_not_var c' &
            { { fresh t1, t1', t2, t2' in c' == CEq (t1', t2') & c == CEq (t1, t2)
                & eq_t t1 t1' & eq_t t2 t2' }
            | { fresh t1, t1', t2, t2' in c' == CInd (t1', t2') & c == CInd (t1, t2)
                & eq_t t1 t1' & eq_t t2 t2' }
            | { fresh t1, t1', ts, ts', t2, t2' in c' == CCall (t1', ts', t2')
                & c == CCall (t1, ts, t2) & eq_t t1 t1' & eq_t t2 t2' & eq_t_list ts ts' }
            | { fresh t1, t1', ps, ps' in c' == CMatch (t1', ps') & c == CMatch (t1, ps)
                & eq_t t1 t1' & eq_list eq_p ps ps' }
            | { fresh x, t1, t1', ts, ts' in c' == CSexp (x, t1', ts') & c == CSexp (x, t1, ts)
                & eq_t t1 t1' & eq_list eq_t ts ts' }
            }
        | is_not_var c &
            { { fresh t1, t1', t2, t2' in c == CEq (t1, t2) & c' == CEq (t1', t2')
                & eq_t t1 t1' & eq_t t2 t2' }
            | { fresh t1, t1', t2, t2' in c == CInd (t1, t2) & c' == CInd (t1', t2')
                & eq_t t1 t1' & eq_t t2 t2' }
            | { fresh t1, t1', ts, ts', t2, t2' in c == CCall (t1, ts, t2)
                & c' == CCall (t1', ts', t2') & eq_t t1 t1' & eq_t t2 t2' & eq_t_list ts ts' }
            | { fresh t1, t1', ps, ps' in c == CMatch (t1, ps) & c' == CMatch (t1', ps')
                & eq_t t1 t1' & eq_list eq_p ps ps' }
            | { fresh x, t1, t1', ts, ts' in c == CSexp (x, t1, ts) & c' == CSexp (x, t1', ts')
                & eq_t t1 t1' & eq_list eq_t ts ts' }
            }
        }
    }

let ( =~= ) = eq_t
let ( =~~= ) = eq_t_list

(* FIXME problem with lifting unification variables... *)
let rec lift_var_r min add n n' = ocanren
    { min == 0 & Nat.addo add n n'
    | fresh min' in min == Nat.s min' &
        { n == 0 & n' == 0
        | fresh n1, n1' in n == Nat.s n1 & n' == Nat.s n1' & lift_var_r min' add n1 n1'
        }
    }

let rec lift_vars_t_r min add t t' = ocanren
    { { fresh n, n' in t == TName n & t' == TName n' & lift_var_r min add n n' }
    | t == TInt & t' == TInt
    | t == TString & t' == TString
    | { fresh t1, t1' in t == TArray t & t' == TArray t' & lift_vars_t_r min add t1 t1' }
    | { fresh xs, xs' in t == TSexp xs & t' == TSexp xs'
        & List.mapo (lift_vars_sexp_r min add) xs xs' }
    | { fresh n, min', c, c', ts, ts', t1, t1' in t == TArrow (n, c, ts, t1)
        & t' == TArrow (n, c', ts', t1') & Nat.addo n min min'
        & List.mapo (lift_vars_c_r min' add) c c' & List.mapo (lift_vars_t_r min' add) ts ts'
        & lift_vars_t_r min' add t1 t1' }
    | { fresh t1, t1' in t == TMu t1 & t' == TMu t1' & lift_vars_t_r (Nat.s min) add t1 t1' }
    }

and lift_vars_sexp_r min add xts xts' = ocanren {
    fresh x, ts, ts' in xts == (x, ts) & xts' == (x, ts')
        & List.mapo (lift_vars_t_r min add) ts ts'
}

and lift_vars_p_r min add p p' = ocanren
    { p == PWildcard & p' == PWildcard
    | { fresh t, t', p1, p1' in p == PTyped (t, p1) & p' == PTyped (t', p1')
        & lift_vars_t_r min add t t' & lift_vars_p_r min add p1 p1' }
    | { fresh ps, ps' in p == PArray ps & p' == PArray ps'
        & List.mapo (lift_vars_p_r min add) ps ps' }
    | { fresh x, ps, ps' in p == PSexp (x, ps) & p' == PSexp (x, ps')
        & List.mapo (lift_vars_p_r min add) ps ps' }
    | p == PBoxed & p' == PBoxed
    | p == PUnboxed & p' == PUnboxed
    | p == PStringTag & p' == PStringTag
    | p == PArrayTag & p' == PArrayTag
    | p == PSexpTag & p' == PSexpTag
    | p == PFunTag & p' == PFunTag
    }

and lift_vars_c_r min add c c' = ocanren
    { { fresh t1, t1', t2, t2' in c == CEq (t1, t2) & c' == CEq (t1', t2')
        & lift_vars_t_r min add t1 t1' & lift_vars_t_r min add t2 t2' }
    | { fresh t1, t1', t2, t2' in c == CInd (t1, t2) & c' == CInd (t1', t2')
        & lift_vars_t_r min add t1 t1' & lift_vars_t_r min add t2 t2' }
    | { fresh n, ts, ts', t1, t1' in c == CCall (n, ts, t1) & c' == CCall (n, ts', t1')
        & List.mapo (lift_vars_t_r min add) ts ts' & lift_vars_t_r min add t1 t1' }
    | { fresh t1, t1', ps, ps' in c == CMatch (t1, ps) & c' == CMatch (t1', ps')
        & lift_vars_t_r min add t1 t1' & List.mapo (lift_vars_p_r min add) ps ps' }
    | { fresh x, t1, t1', ts, ts' in c == CSexp (x, t1, ts) & c' == CSexp (x, t1', ts')
        & lift_vars_t_r min add t1 t1' & List.mapo (lift_vars_t_r min add) ts ts' }
    }

let lift_vars_subst min add =
    let f nt nt' = ocanren {
        fresh n, n', t, t' in nt == (n, t) & nt' == (n', t')
            & lift_var_r min add n n' & lift_vars_t_r min add t t'
    } in

    List.mapo f

let dbg x = debug_var x (fun _ _ -> ()) (fun _ -> print_endline "oaoaoa" ; success)

let rec subst_v x s t = ocanren
    { s == [] & t == TName x
    | fresh x', t', s' in s == (x', t') :: s' &
        { x' == x & t =~= t'
        | x' =/= x & subst_v x s' t
        }
    }

let rec subst_t s t t' =
    (*
    debug_var t (Fun.flip reify_lama_t) (fun t ->
        debug_var t' (Fun.flip reify_lama_t) (fun t' ->
            debug_var s (Fun.flip reify_subst) (fun s ->
                Printf.printf "subst : %s |- %s -> %s\n"
                    (GT.show GT.list (GT.show logic_lama_t) t)
                    (GT.show GT.list show_subst s)
                    (GT.show GT.list (GT.show logic_lama_t) t') ;
                success))) &&&
    *)
    ocanren
    { s == [] & t =~= t'
    | s =/= [] &
        { { fresh x in t == TName x & subst_v x s t' }
        | t == TInt & t' == TInt
        | t == TString & t' == TString
        | { fresh at, at' in t == TArray at & t' == TArray at' & subst_t s at at' }
        | { fresh xs, xs' in t == TSexp xs & t' == TSexp xs' & List.mapo (subst_sexp s) xs xs' }
        | { fresh fn, s', fc, fc', fts, fts', ft, ft' in t == TArrow (fn, fc, fts, ft)
            & t' == TArrow (fn, fc', fts', ft') & lift_vars_subst 0 fn s s'
            & List.mapo (subst_c s') fc fc' & subst_t s' ft ft'
            & List.mapo (subst_t s') fts fts' }
        | { fresh x, s', t1, t1' in t == TMu t1 & t' == TMu t1'
            & is_not_var x & lift_vars_subst 0 1 s s' & subst_t s' t1 t1' }
        }
    }

and subst_sexp s xts xts' = ocanren
    { s == [] & xts == xts'
    | s =/= [] & fresh x, ts, ts' in xts == (x, ts) & xts' == (x, ts')
        & List.mapo (subst_t s) ts ts'
    }

and subst_p s p p' = ocanren
    { s == [] & eq_p p p'
    | s =/= [] &
        { p == PWildcard & p' == PWildcard
        | { fresh t, t', p1, p1' in p == PTyped (t, p1) & p' == PTyped (t', p1')
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
    }

and subst_c s c c' =
    (*
    debug_var c (Fun.flip reify_lama_c) (fun c ->
        debug_var c' (Fun.flip reify_lama_c) (fun c' ->
            debug_var s (Fun.flip reify_subst) (fun s ->
                Printf.printf "subst : %s |- %s -> %s\n"
                    (GT.show GT.list (GT.show logic_lama_c) c)
                    (GT.show GT.list show_subst s)
                    (GT.show GT.list (GT.show logic_lama_c) c') ;
                success))) &&&
    *)
    ocanren
    { s == [] & eq_c c c'
    | s =/= [] & dbg () &
        { { fresh t1, t1', t2, t2' in c == CEq (t1, t2) & c' == CEq (t1', t2')
            & subst_t s t1 t1' & subst_t s t2 t2' }
        | { fresh t1, t1', t2, t2' in c == CInd (t1, t2) & c' == CInd (t1', t2')
            & subst_t s t1 t1' & subst_t s t2 t2' }
        | { fresh f, f', ts, ts', t, t' in c == CCall (f, ts, t) & c' == CCall (f', ts', t')
            & subst_t s f f' & subst_t s t t' & List.mapo (subst_t s) ts ts' }
        | { fresh t, ps, t', ps' in c == CMatch (t, ps) & c' == CMatch (t', ps')
            & subst_t s t t' & List.mapo (subst_p s) ps ps' }
        | { fresh x, t, t', ts, ts' in c == CSexp (x, t, ts) & c' == CSexp (x, t', ts')
            & subst_t s t t' & List.mapo (subst_t s) ts ts' }
        }
    }

(*
(* primitive solving scheduler *)
let schedule c c' rest = ocanren { c == c' :: rest }
*)

(* slow and fair solving scheduler *)
let schedule =
    (* Eq < Call(const) < Sexp < Ind(const) < Match(const) < Ind(var) < Match(var) < Call(var) *)

    let eq          c = ocanren {            c == CEq    (   _, _   )                } in
    let ind_var     c = ocanren { fresh t in c == CInd   (   t, _   ) & is_var     t } in
    let ind_const   c = ocanren { fresh t in c == CInd   (   t, _   ) & is_not_var t } in
    let call_var    c = ocanren { fresh t in c == CCall  (   t, _, _) & is_var     t } in
    let call_const  c = ocanren { fresh t in c == CCall  (   t, _, _) & is_not_var t } in
    let match_var   c = ocanren { fresh t in c == CMatch (   t, _   ) & is_var     t } in
    let match_const c = ocanren { fresh t in c == CMatch (   t, _   ) & is_not_var t } in
    let sexp        c = ocanren {            c == CSexp  (_, _, _   )                } in

    let lt_c c1 c2 res = ocanren
        { eq c1 &
            { eq          c2 & res == false
            | call_const  c2 & res == true
            | sexp        c2 & res == true
            | ind_const   c2 & res == true
            | match_const c2 & res == true
            | ind_var     c2 & res == true
            | match_var   c2 & res == true
            | call_var    c2 & res == true
            }
        | call_const c1 &
            { eq          c2 & res == false
            | call_const  c2 & res == false
            | sexp        c2 & res == true
            | ind_const   c2 & res == true
            | match_const c2 & res == true
            | ind_var     c2 & res == true
            | match_var   c2 & res == true
            | call_var    c2 & res == true
            }
        | sexp c1 &
            { eq          c2 & res == false
            | call_const  c2 & res == false
            | sexp        c2 & res == false
            | ind_const   c2 & res == true
            | match_const c2 & res == true
            | ind_var     c2 & res == true
            | match_var   c2 & res == true
            | call_var    c2 & res == true
            }
        | ind_const c1 &
            { eq          c2 & res == false
            | call_const  c2 & res == false
            | sexp        c2 & res == false
            | ind_const   c2 & res == false
            | match_const c2 & res == true
            | ind_var     c2 & res == true
            | match_var   c2 & res == true
            | call_var    c2 & res == true
            }
        | match_const c1 &
            { eq          c2 & res == false
            | call_const  c2 & res == false
            | sexp        c2 & res == false
            | ind_const   c2 & res == false
            | match_const c2 & res == false
            | ind_var     c2 & res == true
            | match_var   c2 & res == true
            | call_var    c2 & res == true
            }
        | ind_var c1 &
            { eq          c2 & res == false
            | call_const  c2 & res == false
            | sexp        c2 & res == false
            | ind_const   c2 & res == false
            | match_const c2 & res == false
            | ind_var     c2 & res == false
            | match_var   c2 & res == true
            | call_var    c2 & res == true
            }
        | match_var c1 &
            { eq          c2 & res == false
            | call_const  c2 & res == false
            | sexp        c2 & res == false
            | ind_const   c2 & res == false
            | match_const c2 & res == false
            | ind_var     c2 & res == false
            | match_var   c2 & res == false
            | call_var    c2 & res == true
            }
        | call_var c1 &
            { eq          c2 & res == false
            | call_const  c2 & res == false
            | sexp        c2 & res == false
            | ind_const   c2 & res == false
            | match_const c2 & res == false
            | ind_var     c2 & res == false
            | match_var   c2 & res == false
            | call_var    c2 & res == false
            }
        }
    in

    list_minimum lt_c

(*
(* fast and greedy solving scheduler *)
let schedule orig_c c' orig_rest = call_fresh @@ fun tmp_rest ->
    let rec hlp c rest =
        let return = ocanren { orig_rest == tmp_rest & c == c' :: rest } in
        let continue = delay @@ fun () -> ocanren { fresh c1, c2, rest' in c == c1 :: c2
            & rest == c1 :: rest' & hlp c2 rest' } in

        ocanren
        { c == [] & schedule orig_c c' orig_rest (* fallback to simple *)
        | fresh c1 in c == c1 :: _ &
            { c1 == CEq (_, _) & return
            | { fresh t in c1 == CInd (t, _) &
                { is_var t & continue
                | is_not_var t & return
                } }
            | { fresh t in c1 == CCall (t, _, _) &
                { is_var t & continue
                | is_not_var t & return
                } }
            | { fresh t in c1 == CMatch (t, _) &
                { is_var t & continue
                | is_not_var t & return
                } }
            | c1 == CSexp (_, _, _) & return
            }
        }
    in

    hlp orig_c tmp_rest
*)

let rec make_subst n res = ocanren
    { n == 0 & res == []
    | fresh n', t, res' in n == Nat.s n' & res == (n', t) :: res' & make_subst n' res'
    }

let sexp_max_length = Stdlib.ref Int.max_int
let sexp_max_args = Stdlib.ref Int.max_int

type match_t_res =
    ( (injected_lama_t, injected_lama_p) Pair.injected List.injected
    , (injected_lama_t, injected_lama_t) Pair.injected List.injected
    ) Pair.injected

(* assumes that t is not Mu *)
let rec match_t t p (res : match_t_res Option.groundi) =
    let some = Option.some in

    let wildcard_sexp_hlp =
        let max_args = !sexp_max_args in

        let check_n n = if n > max_args then failure else success in

        let rec wildcard_sexp_hlp n ts tps = let n' = n + 1 in ocanren { check_n n &
            { ts == [] & tps == []
            | fresh t, ts', tps' in ts == t :: ts' & tps == (t, PWildcard) :: tps'
                & wildcard_sexp_hlp n' ts' tps'
            }
        } in

        wildcard_sexp_hlp 0
    in

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
        | fresh p, ps' in ps == p :: ps' &
            { ts == [] & res == None
            | fresh t, ts', res' in ts == t :: ts' & sexp_hlp ts' ps' res' &
                { res' == None & res == None
                | fresh tps in res' == Some tps & res == Some ((t, p) :: tps)
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

    ocanren
    { p == PWildcard &
        { t == TName _ & res == some ([], []) (* MT-WildcardVar *)
        | t =/= TName _ &
            { t == TInt & res == some ([], []) (* MT-WildcardInt *)
            | t =/= TInt &
                { t == TString & res == some ([], []) (* MT-WildcardString *)
                | t =/= TString &
                    { { fresh t' in t == TArray t' & res == some ([(t', PWildcard)], []) } (* MT-WildcardArray *)
                    | t =/= TArray _ &
                        { { fresh ts, tps in t == TSexp [(_, ts)] & res == some (tps, [])
                            & wildcard_sexp_hlp ts tps } (* MT-WildcardSexp *)
                        | t =/= TSexp _ &
                            { t == TArrow (_, _, _, _) & res == some ([], []) (* MT-WildcardFun *)
                            | t =/= TArrow (_, _, _, _) &
                                { t == TMu _ & res == some ([], []) (* hack for Mu *)
                                | t =/= TMu _ & res == None
                                }
                            }
                        }
                    }
                }
            }
        }
    | { fresh s, p', res' in p == PTyped (s, p') & match_t t p' res' &
        { res' == None & res == None
        | fresh ps, eqs in res' == some (ps, eqs) & res == some (ps, (t, s) :: eqs) (* MT-Typed *)
        } }
    | { fresh ps in p == PArray ps &
        { t =/= TArray _ & res == None
        | fresh t', tps in t == TArray t' & res == some (tps, []) & array_hlp t' ps tps (* MT-Array *)
        } }
    | { fresh x, ps in p == PSexp (x, ps) &
        { t =/= TSexp [(x, _)] & res == None
        | fresh ts, res' in t == TSexp [(x, ts)] & sexp_hlp ts ps res' &
            { res' == None & res == None
            | fresh tps in res' == Some tps & res == some (tps, []) (* MT-Sexp *)
            }
        } }
    | p == PBoxed &
        { t == TString & res == some ([], []) (* MT-BoxString *)
        | t =/= TString &
            { { fresh t' in t == TArray t' & res == some ([(t', PWildcard)], []) } (* MT-BoxArray *)
            | t =/= TArray _ &
                { { fresh ts, tps in t == TSexp [(_, ts)] & res == some (tps, [])
                    & wildcard_sexp_hlp ts tps } (* MT-BoxSexp *)
                | t =/= TSexp _ &
                    { t == TArrow (_, _, _, _) & res == some ([], []) (* MT-BoxArrow *)
                    | t =/= TArrow (_, _, _, _) & res == None
                    }
                }
            }
        }
    | p == PUnboxed &
        { t == TInt & res == some ([], []) (* MT-IntShape *)
        | t =/= TInt & res == None
        }
    | p == PStringTag &
        { t == TString & res == some ([], []) (* MT-StringShape *)
        | t =/= TString & res == None
        }
    | p == PArrayTag &
        { { fresh t' in t == TArray t' & res == some ([(t', PWildcard)], []) } (* MT-ArrayShape *)
        | t =/= TArray _ & res == None
        }
    | p == PSexpTag &
        { { fresh ts, tps in t == TSexp [(_, ts)] & res == some (tps, [])
            & wildcard_sexp_hlp ts tps } (* MT-SexpShape *)
        | t =/= TSexp _ & res == None
        }
    | p == PFunTag &
        { t == TArrow (_, _, _, _) & res == some ([], []) (* MT-FunShape *)
        | t =/= TArrow (_, _, _, _) & res == None
        }
    }

let ind_sexp_hlp xs (t : injected_lama_t) : goal =
    let max_length = !sexp_max_length in
    let max_args = !sexp_max_args in

    let check_n n = if n > max_args then failure else success in

    let rec hlp n ts = let n' = n + 1 in ocanren { check_n n &
        { ts == []
        | fresh t', ts' in ts == t' :: ts' & t =~= t' & hlp n' ts'
        }
    } in

    let hlp ts = hlp 0 ts in

    let check_n n = if n > max_length then failure else success in

    let rec f n xs = let n' = n + 1 in ocanren { check_n n &
        { xs == []
        | fresh ts, xs' in xs == (_, ts) :: xs' & hlp ts & f n' xs'
        }
    } in

    f 0 xs

(* assumes that t is not Mu *)
let match_t_ast t ps c =
    let some = Option.some in
    let o = Nat.o in
    let s = Nat.s in

    let rec eqs_hlp eqs = ocanren
        { eqs == []
        | fresh t, t', eqs' in eqs == (t, t') :: eqs' & t =~= t' & eqs_hlp eqs'
        }
    in

    let rec match_hlp ps num tps = ocanren
        { ps == [] & num == o & tps == []
        | fresh p, ps', res in ps == p :: ps' & match_t t p res &
            { res == None & match_hlp ps' num tps
            | fresh tps', tps'', num', eqs in res == some (tps', eqs)
                & num == s num' & eqs_hlp eqs & List.appendo tps' tps'' tps
                & match_hlp ps' num' tps''
            }
        }
    in

    let rec match_c_hlp tps c = ocanren
        { tps == [] & c == []
        | fresh t, ps, tps', c2 in tps == (t, ps) :: tps' & c == (CMatch (t, ps)) :: c2
            & match_c_hlp tps' c2
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

    ocanren { fresh num, tps, tps' in num =/= o & match_hlp ps num tps
        & group_by_fst tps tps' & match_c_hlp tps' c } (* MT-Ast *)

let match_sexp_hlp ps =
    let max_length = !sexp_max_length in

    let check_n n = if n > max_length then failure else success in

    let rec hlp n xs c = let n' = n + 1 in ocanren { check_n n &
        { xs == [] & c == []
        | fresh xts, xs', c1, c2 in xs == xts :: xs' & match_t_ast (TSexp [xts]) ps c1
            & List.appendo c1 c2 c & hlp n' xs' c2
        }
    } in

    hlp 0

let sexp_x_hlp (x : int ilogic) xs (ts : injected_lama_t List.injected) : goal =
    (* We want here to require that xs contains label x with types ts and all other labels
     * is NOT label x
     * We would like to require it using only logical language, but in that case we will get
     * answers with constrained labels that isn't any of requested label but isn't any concrete
     * label at all
     * So we must check additionally that any of labels that are before label x,
     * are concrete, not logic variables
     * In such case we will get only Sexp types with concrete labels
     * and dramatically shrink search space
     * Additionally, we assumes that any x passed to this relation is concrete,
     * don't assert that to not slow down
     *)

    let max_length = !sexp_max_length in

    let check_n n = if n > max_length then failure else success in

    (* require that xs doesn't contain label x *)
    let rec not_in_tail n xs = let n' = n + 1 in ocanren { check_n n &
        { xs == []
        | fresh x', xs' in xs == (x', _) :: xs'
            & x =/= x' & not_in_tail n' xs'
        }
    } in

    (* require that xs contains exactly one label x with correct types *)
    let rec hlp n xs = let n' = n + 1 in ocanren { check_n n &
        { fresh x', ts', xs' in xs == (x', ts') :: xs' &
            { x == x' & ts =~~= ts' & not_in_tail n' xs'
            | is_not_var x' & x =/= x' & hlp n' xs'
            }
        }
    } in

    hlp 0 xs

(* unfolds Mu in t if t is exactly Mu in current state *)
let unmu t t' =
    (*
    debug_var t (Fun.flip reify_lama_t) (fun t ->
        debug_var t' (Fun.flip reify_lama_t) (fun t' ->
            Printf.printf "unmu: %s ~ %s" (GT.show GT.list (GT.show logic_lama_t) t) (GT.show GT.list (GT.show logic_lama_t) t') ;
            print_newline () ;
            success)) &&&
    *)
    ocanren
    { is_var t & t == t'
    | is_not_var t &
        { t =/= TMu _ & t == t'
        | fresh t1 in t == TMu t1 & subst_t [(0, t)] t1 t'
        }
    }

let rec ( //- ) c c' : goal =
    let ent_one c c' rest : goal =
        let rec hlp c = ocanren {
            fresh c1, c2 in c == c1 :: c2 &
                { c1 == c' (* C-Refl + C-AndL *)
                | c1 =/= c' & hlp c2 (* C-AndR *)
                }
        } in

        let now_rest = ocanren { c //- rest } in
        let now_rest_with c' = ocanren { fresh c'' in List.appendo c' rest c'' & c //- c'' } in

        (*
        debug_var c (Fun.flip @@ List.reify reify_lama_c) (fun c ->
            debug_var c' (Fun.flip reify_lama_c) (fun c' ->
                debug_var rest (Fun.flip @@ List.reify reify_lama_c) (fun rest ->
                    Printf.printf "%s ||- %s ; %s"
                        (GT.show GT.list (GT.show List.logic @@ GT.show logic_lama_c) c)
                        (GT.show GT.list (GT.show logic_lama_c) c')
                        (GT.show GT.list (GT.show List.logic @@ GT.show logic_lama_c) rest) ;
                    print_newline () ;
                    success))) &&&
        *)

        ocanren
        { hlp c & now_rest (* inferring from context by C-Refl, C-AndL and C-AndR *)
        | { fresh t, t' in c' == CEq (t, t') & t =~= t' & now_rest }
        | { fresh t1, t2 in c' == CInd (t1, t2) & unmu t1 TString & unmu t2 TInt
            & now_rest } (* C-IndString *)
        | { fresh t1, t1', t2 in c' == CInd (t1, t2) & unmu t1 (TArray t1')
            & t1' =~= t2 & now_rest } (* C-IndArray *)
        | { fresh t1, t2, xs in c' == CInd (t1, t2) & unmu t1 (TSexp xs)
            & ind_sexp_hlp xs t2 & now_rest } (* C-IndSexp *)
        | { fresh f, fn, s, fc, fc', fts, ft, ts, t in c' == CCall (f, ts, t)
            & unmu f (TArrow (fn, fc, fts, ft))
            & { is_var fn & fn == 0 | is_not_var fn }
            & { is_var fc & fc == [] | is_not_var fc }
            & make_subst fn s
            & subst_t s ft t & List.mapo (subst_c s) fc fc' & List.mapo (subst_t s) fts ts
            & now_rest_with fc' } (* C-Call *)
        | { fresh t, ps, c'' in c' == CMatch (t, ps) & unmu t TInt
            & match_t_ast TInt ps c'' & now_rest_with c'' } (* C-MatchInt *)
        | { fresh t, ps, c'' in c' == CMatch (t, ps) & unmu t TString
            & match_t_ast TString ps c'' & now_rest_with c'' } (* C-MatchString *)
        | { fresh t, t', ps, c'' in c' == CMatch (t, ps) & unmu t (TArray t')
            & match_t_ast (TArray t') ps c'' & now_rest_with c'' } (* C-MatchArray *)
        | { fresh t, xs, ps, c'' in c' == CMatch (t, ps) & unmu t (TSexp xs)
            & match_sexp_hlp ps xs c'' & now_rest_with c'' } (* C-MatchSexp *)
        | { fresh f, fn, fc, fts, ft, ps, c'' in c' == CMatch (f, ps)
            & unmu f (TArrow (fn, fc, fts, ft))
            & match_t_ast (TArrow (fn, fc, fts, ft)) ps c''
            & now_rest_with c'' } (* C-MatchFun *)
        | { fresh t, ps, c'' in c' == CMatch (TMu t, ps) & is_not_var t
            & match_t_ast (TMu t) ps c'' & now_rest_with c'' } (* hack for Mu *)
        | { fresh t, x, xs, ts in c' == CSexp (x, t, ts) & unmu t (TSexp xs)
            & sexp_x_hlp x xs ts & now_rest } (* C-Sexp *)
        }
    in

    ocanren
    { c' == [] (* C-Top *)
    | fresh c'', rest in schedule c' c'' rest & ent_one c c'' rest
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

let make_project get_sexp =
    let prev_tv_idx = Stdlib.ref 0 in

    let new_tv_idx () =
        let idx = !prev_tv_idx + 1 in
        prev_tv_idx := idx ;
        idx
    in

    let rec inner_scope ?(n=1) sc =
        if n = 0 then sc else inner_scope ~n:(n - 1) (new_tv_idx () :: sc)
    in

    let rec project_t sc : ground_lama_t -> TT.t = function
    | TName n -> `Name (OrigList.nth sc @@ Nat.to_int n)
    | TInt -> `Int
    | TString -> `String
    | TArray t -> `Array (project_t sc t)
    | TSexp xs -> `Sexp (OrigList.map (fun (x, ts) ->
        get_sexp x, OrigList.map (project_t sc) ts) xs)

    | TArrow (n, c, ts, t) ->
        let n = Nat.to_int n in
        let sc = inner_scope ~n sc in
        let xs = TT.IS.of_seq @@ Seq.take n @@ OrigList.to_seq sc in
        `Arrow (xs, OrigList.map (project_c sc) c, OrigList.map (project_t sc) ts, project_t sc t)

    | TMu t -> let sc = inner_scope sc in `Mu (OrigList.hd sc, project_t sc t)

    and project_p sc : ground_lama_p -> TT.p = function
    | PWildcard -> `Wildcard
    | PTyped (t, p) -> `Typed (project_t sc t, project_p sc p)
    | PArray ps -> `Array (OrigList.map (project_p sc) ps)
    | PSexp (x, ps) -> `Sexp (get_sexp x, OrigList.map (project_p sc) ps)
    | PBoxed -> `Boxed
    | PUnboxed -> `Unboxed
    | PStringTag -> `StringTag
    | PArrayTag -> `ArrayTag
    | PSexpTag -> `SexpTag
    | PFunTag -> `FunTag

    and project_c sc : ground_lama_c -> TT.c = function
    | CEq (l, r) -> `Eq (project_t sc l, project_t sc r)
    | CInd (l, r) -> `Ind (project_t sc l, project_t sc r)
    | CCall (t, ss, s) -> `Call (project_t sc t, OrigList.map (project_t sc) ss, project_t sc s)
    | CMatch (t, ps) -> `Match (project_t sc t, OrigList.map (project_p sc) ps)
    | CSexp (x, t, ts) -> `Sexp (get_sexp x, project_t sc t, OrigList.map (project_t sc) ts)
    in

    object

        method t = project_t
        method p = project_p
        method c = project_c
    end

module Subst = TT.Subst
module SM = Map.Make(String)

let make_inject () =
    let module M = Monad in
    let open M.Syntax in

    let free_vars = Stdlib.ref Subst.empty in
    let sexp_labels = Stdlib.ref SM.empty in
    let sexp_max_args = Stdlib.ref 0 in

    (* cache_sexp label size - convert label to unique number *)
    let cache_sexp x n =
        sexp_max_args := Int.max !sexp_max_args n ;

        let x = Printf.sprintf "%s_%d" x n in

        try SM.find x !sexp_labels
        with Not_found ->
            let cur_sl = !sexp_labels in

            let idx = SM.cardinal cur_sl in
            sexp_labels := SM.add x idx cur_sl ;

            idx
    in

    let rec inject_list f = function
    | [] -> M.return @@ List.nil ()
    | x :: xs ->
        let* x = f x in
        let* xs = inject_list f xs in
        M.return @@ List.cons x xs
    in

    let rec inject_t (sc : int Subst.t) : TT.t -> injected_lama_t M.t = function
    | `Name x -> begin match Subst.find_opt x sc with
        | Some n -> M.return @@ tName @@ Nat.nat @@ Nat.of_int n
        | None -> begin match Subst.find_opt x !free_vars with
            | None -> let* fv = call_fresh in free_vars := Subst.add x fv !free_vars ; M.return fv
            | Some t -> M.return t
            end
        end

    | `Int -> M.return @@ tInt ()
    | `String -> M.return @@ tString ()
    | `Array t -> let* t = inject_t sc t in M.return @@ tArray t
    | `Sexp xs -> let* xs = inject_list (inject_sexp sc) xs in M.return @@ tSexp xs

    | `Arrow (xs, c, ts, t) ->
        let n = TT.IS.cardinal xs in

        let sc = Subst.map (fun m -> n + m) sc in
        let sc = Seq.fold_lefti (fun sc n x -> Subst.add x n sc) sc @@ TT.IS.to_seq xs in

        let* c = inject_list (inject_c sc) c in
        let* ts = inject_list (inject_t sc) ts in
        let* t = inject_t sc t in

        M.return @@ tArrow (Nat.nat @@ Nat.of_int n) c ts t

    | `Mu (x, t) ->
        let sc = Subst.add x 0 @@ Subst.map (fun m -> m + 1) sc in
        let* t = inject_t sc t in
        M.return @@ tMu t

    and inject_sexp sc (x, ts) =
        let x = cache_sexp x @@ OrigList.length ts in

        let* ts = inject_list (inject_t sc) ts in
        M.return !!(!!x, ts)

    and inject_p sc : TT.p -> injected_lama_p M.t = function
    | `Wildcard -> M.return @@ pWildcard ()
    | `Typed (t, p) ->
        let* t = inject_t sc t in
        let* p = inject_p sc p in
        M.return @@ pTyped t p

    | `Array ps ->
        let* ps = inject_list (inject_p sc) ps in
        M.return @@ pArray ps

    | `Sexp (x, ps) ->
        let x = cache_sexp x @@ OrigList.length ps in

        let* ps = inject_list (inject_p sc) ps in
        M.return @@ pSexp !!x ps

    | `Boxed -> M.return @@ pBoxed ()
    | `Unboxed -> M.return @@ pUnboxed ()
    | `StringTag -> M.return @@ pStringTag ()
    | `ArrayTag -> M.return @@ pArrayTag ()
    | `SexpTag -> M.return @@ pSexpTag ()
    | `FunTag -> M.return @@ pFunTag ()

    and inject_c sc : TT.c -> injected_lama_c M.t = function
    | `Eq (l, r) ->
        let* l = inject_t sc l in
        let* r = inject_t sc r in
        M.return @@ cEq l r

    | `Ind (l, r) ->
        let* l = inject_t sc l in
        let* r = inject_t sc r in
        M.return @@ cInd l r

    | `Call (t, ss, s) ->
        let* t = inject_t sc t in
        let* ss = inject_list (inject_t sc) ss in
        let* s = inject_t sc s in
        M.return @@ cCall t ss s

    | `Match (t, ps) ->
        let* t = inject_t sc t in
        let* ps = inject_list (inject_p sc) ps in
        M.return @@ cMatch t ps

    | `Sexp (x, t, ts) ->
        let x = cache_sexp x @@ OrigList.length ts in

        let* t = inject_t sc t in
        let* ts = inject_list (inject_t sc) ts in

        M.return @@ cSexp !!x t ts
    in

    object

        method free_vars = !free_vars
        method sexp_labels = !sexp_labels
        method sexp_max_args = !sexp_max_args

        method list = inject_list
        method t = inject_t
        method c = inject_c
    end

let solve (c : TT.c list) : TT.t Subst.t =
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

    let make_goal ans : goal = inject#list (inject#c Subst.empty) c (fun c ->
        let free_vars = Subst.to_seq inject#free_vars in

        print_string "Free variables: " ;
        Seq.iter (Printf.printf "%d ") @@ Seq.map fst free_vars ;
        print_newline () ;

        let free_vars = GT.foldr GT.list (Fun.flip List.cons) (List.nil ())
            @@ OrigList.of_seq @@ Seq.map snd free_vars in

        (* set max length for any Sexp type *)
        sexp_max_length := SM.cardinal inject#sexp_labels ;

        (* set max number of args of Sexp constructor *)
        sexp_max_args := inject#sexp_max_args ;

        Printf.printf "Max Sexp labels: %d\n" !sexp_max_length ;
        Printf.printf "Max args of Sexp ctor: %d\n" !sexp_max_args ;

        ocanren { ans == free_vars & [] //- c }
    ) in

    let res = run q make_goal (fun x -> x#reify @@ List.prj_exn reify_lama_t) in

    let ans = Stream.take ~n:1 @@ Stream.map Stdlib.Option.get
        @@ Stream.filter Stdlib.Option.is_some @@ Stream.map (fun ans ->
            try Some (OrigList.map logic_lama_t_to_ground ans)
            with _ -> None
        ) res
    in

    let ans = match ans with
    | [] -> failwith "no one solution found"
    | [ans] -> ans
    | _ -> failwith "not reachable"
    in

    print_endline @@ "Answer: " ^ GT.show GT.list (GT.show ground_lama_t) ans ;

    let free_vars = Seq.map fst @@ Subst.to_seq inject#free_vars in

    let subst = Seq.fold_left (fun subst (v, t) -> Subst.add v t subst) Subst.empty
        @@ Seq.zip free_vars @@ OrigList.to_seq ans in

    if Subst.cardinal subst <> Seq.length free_vars then failwith "wrong substitution size" ;

    let module IM = Map.Make(Int) in

    let sexp_labels_inv = IM.of_seq
        @@ Seq.map (fun (x, l) -> l, x)
        @@ SM.to_seq inject#sexp_labels
    in

    let get_sexp x = IM.find x sexp_labels_inv in
    let project = make_project get_sexp in

    Subst.map (project#t []) subst
