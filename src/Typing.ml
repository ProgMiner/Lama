
open GT

module Pattern = Language.Pattern

module Expr = struct

    @type t =
    | Scope     of decl list * t    (* scope expression *)
    | Seq       of t * t            (* sequence point *)
    | Assign    of t * t            (* assignment *)
    | Binop     of t * t            (* binary operator *)
    | Call      of t * t list       (* call *)
    | Subscript of t * t            (* subscript *)
    | Name      of string           (* variable name *)
    | Int       of int              (* integer *)
    | String    of string           (* string *)
    | Lambda    of string list * t  (* lambda expression *)
    | Skip                          (* skip *)
    | Array     of t list           (* array *)
    | Sexp      of string * t list  (* S-expression *)
    | If        of t * t * t        (* if-then-else *)
    | While     of t * t            (* while loop *)
    | DoWhile   of t * t            (* do-while loop *)
    | Case      of t * (Pattern.t * t) list (* case-of *)

    and decl =
    | Var of string * t
    | Fun of string * string list * t
    with show, eval

    let decl_name = function
    | Var (x, _) -> x
    | Fun (x, _, _) -> x

    module L = Language.Expr

    let rec from_language = function
    | L.Const x -> Int x
    | L.Array xs -> Array (List.map from_language xs)
    | L.String x -> String x
    | L.Sexp (x, xs) -> Sexp (x, List.map from_language xs)
    | L.Var x -> Name x
    | L.Ref x -> Name x
    | L.Binop (_, l, r) -> Binop (from_language l, from_language r)
    | L.Elem (xs, i) -> Subscript (from_language xs, from_language i)
    | L.ElemRef (xs, i) -> Subscript (from_language xs, from_language i)
    | L.Call (f, xs) -> Call (from_language f, List.map from_language xs)
    | L.Assign (l, r) -> Assign (from_language l, from_language r)
    | L.Seq (l, r) -> Seq (from_language l, from_language r)
    | L.Skip -> Skip
    | L.If (c, t, f) -> If (from_language c, from_language t, from_language f)
    | L.While (c, b) -> While (from_language c, from_language b)
    | L.DoWhile (b, c) -> DoWhile (from_language b, from_language c)
    | L.Case (x, bs, _, _) -> Case ( from_language x
                                   , List.map (fun (p, b) -> (p, from_language b)) bs
                                   )
    | L.Ignore t -> from_language t
    | L.Unit -> Int 0
    | L.Scope (ds, t) -> Scope (List.map decl_from_language ds, from_language t)
    | L.Lambda (xs, b) -> Lambda (xs, from_language b)
    | L.Leave -> invalid_arg "Leave"
    | L.Intrinsic _ -> invalid_arg "Intrinsic"
    | L.Control _ -> invalid_arg "Control"

    and decl_from_language = function
    | x, (_, `Fun      (xs,  t)) -> Fun (x, xs, from_language t)
    | x, (_, `Variable  None   ) -> Var (x, Int 0)
    | x, (_, `Variable (Some t)) -> Var (x, from_language t)
end

module Type = struct

    module IS = Set.Make(Int)
    module Context = Map.Make(String)
    module Subst = Map.Make(Int)

    type t = [
    | `Name     of int              (* type variable name *)
    | `Int                          (* integer *)
    | `String                       (* string *)
    | `Array    of t                (* array *)
    | `Sexp     of (string * t list) list (* S-expression *)
    | `Arrow    of IS.t * c * t list * t (* arrow *)
    | `Mu       of int * t          (* mu-type *)
    ]

    and p = [
    | `Wildcard
    | `Typed    of t * p
    | `Array    of p list
    | `Sexp     of string * p list
    | `Boxed
    | `Unboxed
    | `StringTag
    | `ArrayTag
    | `SexpTag
    | `FunTag
    ]

    and c = [
    | `Top                          (* always true *)
    | `And      of c * c            (* logical AND *)
    | `Eq       of t * t            (* syntax equality *)
    | `Ind      of t * t            (* indexable *)
    | `Call     of t * t list * t   (* callable with args and result types *)
    | `Match    of t * p list       (* match type with patterns *)
    | `Sexp     of string * t * t list (* sexp with label and types *)
    ]

    let show_is is = match IS.elements is with
    | i :: is -> (List.fold_left (Printf.sprintf "%s, %d") (Printf.sprintf "{%d" i) is) ^ "}"
    | [] -> "{}"

    let rec show_t : t -> _ = function
    | `Name x -> Printf.sprintf "tv_%d" x
    | `Int -> "Int"
    | `String -> "String"
    | `Array t -> Printf.sprintf "[%s]" @@ show_t t
    | `Sexp vs -> "Sexp "
        ^ GT.show list (fun (x, ts) -> Printf.sprintf "%s (%s)" x @@ GT.show list show_t ts) vs

    | `Arrow (xs, c, ts, t) -> Printf.sprintf "forall (%s). (%s) => (%s) -> %s"
        (show_is xs) (show_c c) (GT.show list show_t ts) (show_t t)

    | `Mu (x, t) -> Printf.sprintf "mu %d. %s" x @@ show_t t

    and show_p : p -> _ = function
    | `Wildcard -> "_"
    | `Typed (t, p) -> Printf.sprintf "%s @ %s" (show_t t) (show_p p)
    | `Array ps -> GT.show list show_p ps
    | `Sexp (x, ps) -> Printf.sprintf "%s %s" x @@ GT.show list show_p ps
    | `Boxed -> "#box"
    | `Unboxed -> "#val"
    | `StringTag -> "#str"
    | `ArrayTag -> "#array"
    | `SexpTag -> "#sexp"
    | `FunTag -> "#fun"

    and show_c : c -> _ = function
    | `Top -> "T"
    | `And (l, r) -> Printf.sprintf "%s && %s" (show_c l) (show_c r)
    | `Eq (l, r) -> Printf.sprintf "%s = %s" (show_t l) (show_t r)
    | `Ind (l, r) -> Printf.sprintf "Ind(%s, %s)" (show_t l) (show_t r)
    | `Call (t, ts, s) -> Printf.sprintf "Call(%s, %s, %s)" (show_t t) (GT.show list show_t ts) (show_t s)
    | `Match (t, ps) -> Printf.sprintf "Match(%s, %s)" (show_t t) (GT.show list show_p ps)
    | `Sexp (x, t, ts) -> Printf.sprintf "Sexp_%s(%s, %s)" x (show_t t) (GT.show list show_t ts)

    (* free type variables *)

    let rec ftv fvs : t -> _ = function
    | `Name x -> IS.add x fvs
    | `Int -> fvs
    | `String -> fvs
    | `Array t -> ftv fvs t
    | `Sexp ps -> List.fold_left (fun fvs (_, ts) -> List.fold_left ftv fvs ts) fvs ps
    | `Arrow (xs, c, ts, t) ->
        let fvs' = List.fold_left ftv IS.empty ts in
        let fvs' = ftv fvs' t in
        let fvs' = ftv_c fvs' c in
        IS.union fvs @@ IS.diff fvs' xs

    | `Mu (x, t) ->
        let fvs' = ftv IS.empty t in
        IS.union fvs @@ IS.remove x fvs'

    and ftv_p fvs : p -> _ = function
    | `Wildcard -> fvs
    | `Typed (t, p) -> ftv_p (ftv fvs t) p
    | `Array ps -> List.fold_left ftv_p fvs ps
    | `Sexp (_, ps) -> List.fold_left ftv_p fvs ps
    | `Boxed -> fvs
    | `Unboxed -> fvs
    | `StringTag -> fvs
    | `ArrayTag -> fvs
    | `SexpTag -> fvs
    | `FunTag -> fvs

    and ftv_c fvs : c -> _ = function
    | `Top -> fvs
    | `And (l, r) -> ftv_c (ftv_c fvs l) r
    | `Eq (l, r) -> ftv (ftv fvs l) r
    | `Ind (l, r) -> ftv (ftv fvs l) r
    | `Call (t, ts, s) -> ftv (List.fold_left ftv (ftv fvs t) ts) s
    | `Match (t, ps) -> List.fold_left ftv_p (ftv fvs t) ps
    | `Sexp (_, t, ts) -> List.fold_left ftv (ftv fvs t) ts

    let ftv_context ctx = Context.fold (fun _ t fvs -> ftv fvs t) ctx IS.empty

    (* substitution *)

    let rec subst_t f bvs : t -> t = function
    | `Name x as t when IS.mem x bvs -> t
    | `Name x -> f x
    | `Int -> `Int
    | `String -> `String
    | `Array t -> `Array (subst_t f bvs t)
    | `Sexp xs -> `Sexp (List.map (fun (x, ts) -> x, List.map (subst_t f bvs) ts) xs)
    | `Arrow (xs, c, ts, t) ->
        let bvs = IS.union bvs xs in
        `Arrow (xs, subst_c f bvs c, List.map (subst_t f bvs) ts, subst_t f bvs t)

    | `Mu (x, t) ->
        let bvs = IS.add x bvs in
        `Mu (x, subst_t f bvs t)

    and subst_p f bvs : p -> p = function
    | `Wildcard -> `Wildcard
    | `Typed (t, p) -> `Typed (subst_t f bvs t, subst_p f bvs p)
    | `Array ps -> `Array (List.map (subst_p f bvs) ps)
    | `Sexp (x, ps) -> `Sexp (x, List.map (subst_p f bvs) ps)
    | `Boxed -> `Boxed
    | `Unboxed -> `Unboxed
    | `StringTag -> `StringTag
    | `ArrayTag -> `ArrayTag
    | `SexpTag -> `SexpTag
    | `FunTag -> `FunTag

    and subst_c f bvs : c -> c = function
    | `Top -> `Top
    | `And (l, r) -> `And (subst_c f bvs l, subst_c f bvs r)
    | `Eq (l, r) -> `Eq (subst_t f bvs l, subst_t f bvs r)
    | `Ind (l, r) -> `Ind (subst_t f bvs l, subst_t f bvs r)
    | `Call (t, ss, s) -> `Call (subst_t f bvs t, List.map (subst_t f bvs) ss, subst_t f bvs s)
    | `Match (t, ps) -> `Match (subst_t f bvs t, List.map (subst_p f bvs) ps)
    | `Sexp (x, t, ts) -> `Sexp (x, subst_t f bvs t, List.map (subst_t f bvs) ts)

    let subst_map_to_fun s x = Option.value (Subst.find_opt x s) ~default:(`Name x)

    (* applies s' to s and adds bindings from s' to s, s' mustn't include bindings of s *)
    let subst_concat s s' =
        let s = Subst.map (subst_t (subst_map_to_fun s') IS.empty) s in
        Subst.union (fun _ -> failwith "duplicated variables in substitution") s s'

    let unfold_mu = function
    | `Mu (x, t) as t' -> subst_t (subst_map_to_fun @@ Subst.singleton x t') IS.empty t
    | t -> t

    (* list of constraints without And and Top *)

    let list_c =
        let rec list_c acc = function
        | `Top -> acc
        | `And (l, r) -> list_c (list_c acc l) r
        | c -> c :: acc
        in list_c []

    (* constraint built from list *)

    let c_list = function
    | [] -> `Top
    (* NB: rope-like structure with "lightweight" left branch, important for solver *)
    | c :: cs -> List.fold_left (fun acc c -> `And (c, acc)) c cs

    let c_list cs = c_list @@ List.rev cs

    (* sort constraints by "complexity" to optimize solving *)

    let sort_cs cs =
        let cmp c1 c2 = match c1, c2 with
        | `Eq _, `Eq _ -> 0
        | `Sexp _, `Sexp _ -> 0
        | `Ind _, `Ind _ -> 0
        | `Call _, `Call _ -> 0
        | `Match _, `Match _ -> 0
        | `Eq _, _ -> -1
        | _, `Eq _ -> 1
        | `Sexp _, _ -> -1
        | _, `Sexp _ -> 1
        | `Ind _, _ -> -1
        | _, `Ind _ -> 1
        | `Call _, _ -> -1
        | _, `Call _ -> 1
        | `Match _, _ -> -1
        | _, `Match _ -> 1
        in

        List.sort cmp cs

    (* solve syntax equality constraints using Robinson's alogrithm *)

    let rec unify : t * t -> _ = function
    | (`Name x, `Name y) when x == y -> Subst.empty
    | (`Name x, `Name y) when x < y -> Subst.singleton y @@ `Name x
    | (`Name x, `Name y) -> Subst.singleton x @@ `Name y
    | (`Name x, t) when IS.mem x @@ ftv IS.empty t -> begin match t with
        | `Mu _ -> failwith "double Mu" (* TODO *)
        | _ -> Subst.singleton x @@ `Mu (x, t)
        end

    | (`Name x, t) -> Subst.singleton x t
    | (t, (`Name _ as t')) -> unify (t', t)
    | (`Int, `Int) -> Subst.empty
    | (`String, `String) -> Subst.empty
    | (`Array t1, `Array t2) -> unify (t1, t2)
    | (`Sexp _, `Sexp _) -> failwith "sexp equality occurred" (* TODO *)
    | (`Arrow _, `Arrow _) -> failwith "arrows equality occurred" (* TODO *)
    | (`Mu _, _) -> failwith "mu-s equality occurred" (* TODO *)
    | (_, `Mu _) -> failwith "mu-s equality occurred" (* TODO *)
    | (l, r) -> failwith @@ Printf.sprintf "cannot unify %s with %s" (show_t l) (show_t r)

    let unify_c =
        let f (s, res) = function
        | `Top -> failwith "ill-formed constraint list (Top)"
        | `And _ -> failwith "ill-formed constraint list (And)"
        | `Eq (l, r) ->
            let sf = subst_map_to_fun s in
            let l = subst_t sf IS.empty l in
            let r = subst_t sf IS.empty r in

            let s' = unify (l, r) in
            subst_concat s s', res

        | c -> s, c :: res
        in

        fun c -> List.fold_left f (Subst.empty, []) c

    (* split constraint by given bound and free type variables *)

    (* Explanation: constraint is an undirected graph with types as nodes and primitive constraints
     *              as edges, so we could split it on two sides: free and bound.
     *
     *              Bound part includes all bound variables and all reachable variables.
     *              Free part is all non-reachable variables.
     *
     *              Free variables argument is used as filter, they are not part of graph.
     *
     *              As a result, we could determine set of bound variables, bound constraints and
     *              free constraints.
     *)

    let split_c bvs fvs (c : c) =
        let bvs = IS.diff bvs fvs in
        let c = List.map (fun c -> c, IS.diff (ftv_c IS.empty c) fvs) @@ list_c c in

        Printf.printf "Source free variables: %s\n"
            @@ GT.show list (GT.show int) @@ List.of_seq @@ IS.to_seq fvs ;

        Printf.printf "Source bound variables: %s\n"
            @@ GT.show list (GT.show int) @@ List.of_seq @@ IS.to_seq bvs ;

        let module Edges = Map.Make(Int) in
        let edges = Stdlib.ref Edges.empty in

        let add_edges tvs tv =
            let cur_edges = !edges in
            let cur = Edges.find_opt tv cur_edges in
            let cur = Option.value cur ~default:IS.empty in
            edges := Edges.add tv (IS.union cur tvs) cur_edges
        in

        (* build graph *)
        List.iter (fun tvs -> IS.iter (add_edges tvs) tvs) @@ List.map snd c ;

        let visited = Stdlib.ref IS.empty in

        let rec dfs tv =
            let cur_visited = !visited in
            if IS.mem tv cur_visited
            then ()
            else (
                visited := IS.add tv cur_visited ;
                IS.iter dfs @@ Option.value (Edges.find_opt tv !edges) ~default:IS.empty ;
            )
        in

        (* mark reachable from bound *)
        IS.iter dfs bvs ;

        (* here is bound part of tvs *)
        let bvs = !visited in

        (* bvs is transitive closure, so check any tv is enough *)
        let pred (_, fvs) = match IS.choose_opt fvs with
        | None -> false
        | Some fv -> IS.mem fv bvs
        in

        let (bc, fc) = List.partition pred c in
        let bc = c_list @@ List.map fst bc in
        let fc = c_list @@ List.map fst fc in

        Printf.printf "Result bound variables: %s\n"
            @@ GT.show list (GT.show int) @@ List.of_seq @@ IS.to_seq bvs ;

        bvs, bc, fc

    (* make inferrer *)

    let make_infer () =
        let module E = Expr in

        let prev_tv_idx = Stdlib.ref 0 in

        let new_tv () =
            let idx = !prev_tv_idx + 1 in
            prev_tv_idx := idx ;
            `Name idx
        in

        (* simplifier
         *
         * Applies following passes:
         * 1. Eq elimination (eliminate Eq(t1, t2) by unification of t1 = t2)
         * 2. Recursive calls flattening (convert mutual recursive Calls into direct recursive Calls)
         *)
        (* TODO simplify better *)

        let simplify =
            let rec simplify fvs (c : c) : c * t Subst.t =
                let c = list_c c in

                let s, c = unify_c c in
                let s, c = apply_rcf fvs s c in
                let c = sort_cs c in

                (* we mustn't use fvs here because there are may Eq(fv1, fv2) *)
                let c = list_c @@ subst_c (subst_map_to_fun s) IS.empty @@ c_list c in

                (* preserve Eq for free variables *)
                let eqs = Seq.filter (fun (x, t) -> IS.mem x fvs) @@ Subst.to_seq s in
                let eqs = Seq.map (fun x, t -> `Eq (`Name x, t)) eqs in
                let c = List.of_seq eqs @ c in

                c_list c, s

            and apply_rcf fvs s c =
                let exception Changed in

                let new_c = Stdlib.ref c in
                let new_s = Stdlib.ref s in

                try
                    Subst.iter (fun x t -> match flatten_recursive_calls fvs new_c t with
                    | Some (t', s') ->
                        let s = Subst.add x t' s in (* s == !new_s *)
                        new_s := subst_concat s s' ;

                        Printf.printf "Recursive calls flattened in tv_%d:\n" x ;
                        Printf.printf "  Before: %s\n" (show_t t) ;
                        Printf.printf "  After : %s\n" (show_t t') ;
                        raise Changed

                    | None -> ()
                    ) s ;

                    s, c

                with Changed -> apply_rcf fvs !new_s !new_c

            (* recursive calls flattening
             *
             * Given type of form (mu x. \/xs. C => (ts) -> t), free variables set (of context)
             *
             * 1. Recursively traverse constraints (only in Call(Arrow(...), ...)) from down to up
             *   a) If there isn't Call(x, ...), keep in untouched
             *   b) If there is Call(x, ...) - unpack all constraints from Call by refreshing
             *      bound variables of Arrow and generating Eq for args and result and refreshed
             *      formal parameters and result types respectively:
             *
             *      x |-rcf- Call(\/xs. (... /\ Call(x, ...) /\ ... = C) => (ts) -> t, taus, tau)
             *                                          ||
             *                                          || ys <- fresh vars
             *                                          \/
             *          C [xs |-> ys] /\ Eq(ts_i [xs |-> ys], taus_i) /\ Eq(t [xs |-> ys], tau)
             *
             * 2. After that we have flatten constraint but with Eq and maybe unbound constraints
             *    so we need to simplify constraints (including Eq elimination so we got
             *    substituion) and split them on bound and free (got new free constraints)
             *
             * TODO deal with Call(Mu(..., Arrow(...))) in Mu(x, Arrow(...))
             *
             * TODO it works wrong with variables that must be free because we don't know
             *      actual FVs that was in place where type was introduced
             *)
            and flatten_recursive_calls =
                let rec rcf x has_rc changed : c -> c = function
                | `Call (`Arrow (xs, c, ts, t), taus, tau) as c' ->
                    if List.length ts <> List.length taus then failwith @@ Printf.sprintf
                        "wrong number of arguments in call (%d expected but %d given)"
                        (List.length ts) (List.length taus) ;

                    let nested_has_rc = Stdlib.ref false in
                    let nested_changed = Stdlib.ref false in
                    let c = List.map (rcf x nested_has_rc nested_changed) @@ list_c c in

                    if !nested_has_rc then
                        let xs = IS.elements xs in
                        let ys = List.map (fun _ -> new_tv ()) xs in

                        let s = List.map2 (fun x y -> x, y) xs ys in
                        let s = Subst.of_seq @@ List.to_seq s in
                        let sf = subst_map_to_fun s in

                        let c = subst_c sf IS.empty @@ c_list c in
                        let ts = List.map (subst_t sf IS.empty) ts in
                        let t = subst_t sf IS.empty t in

                        let eqs = List.map2 (fun t tau -> `Eq (t, tau)) (t :: ts) (tau :: taus) in
                        let eqs = c_list eqs in

                        has_rc := true ;
                        changed := true ;
                        `And (c, eqs)

                    else c'

                | `Call (`Name y, _, _) as c when x = y -> has_rc := true ; c
                | c -> c
                in

                fun fvs new_c : (t -> (t * t Subst.t) option) -> function
                | `Mu (x, `Arrow (_, c, ts, t)) ->
                    let has_rc = Stdlib.ref false in
                    let changed = Stdlib.ref false in

                    let c = List.map (rcf x has_rc changed) @@ list_c c in

                    if !changed then
                        let fvs = IS.add x fvs in
                        let c, s = simplify fvs @@ c_list c in

                        if Subst.mem x s then failwith "recursive variable unified" ;

                        let subst_t' = subst_t (subst_map_to_fun s) IS.empty in
                        let fvs = IS.filter (fun fv -> not @@ Subst.mem fv s) fvs in
                        let ts = List.map subst_t' ts in
                        let t = subst_t' t in

                        let signature_tvs = List.fold_left ftv (ftv IS.empty t) ts in
                        let bvs, bc, fc = split_c signature_tvs fvs c in

                        new_c := list_c fc @ !new_c ;

                        (* we don't eliminate recursion at all so x must present in bc *)
                        Some (`Mu (x, `Arrow (bvs, bc, ts, t)), s)

                    else None

                | _ -> None
            in

            simplify
        in

        let rec infer_p ctx : Pattern.t -> p * t Context.t = function
        | Pattern.Wildcard -> `Wildcard, ctx
        | Pattern.Named (x, p) ->
            let t = new_tv () in
            let ctx = Context.add x t ctx in
            let p, ctx = infer_p ctx p in
            `Typed (t, p), ctx

        | Pattern.Array ps ->
            let ps, ctx = infer_ps ctx ps in
            `Array ps, ctx

        | Pattern.Sexp (x, ps) ->
            let ps, ctx = infer_ps ctx ps in
            `Sexp (x, ps), ctx

        | Pattern.Const _ -> `Unboxed, ctx
        | Pattern.String _ -> `StringTag, ctx
        | Pattern.Boxed -> `Boxed, ctx
        | Pattern.UnBoxed -> `Unboxed, ctx
        | Pattern.StringTag -> `StringTag, ctx
        | Pattern.ArrayTag -> `ArrayTag, ctx
        | Pattern.SexpTag -> `SexpTag, ctx
        | Pattern.ClosureTag -> `FunTag, ctx

        and infer_ps ctx ps =
            let ps, ctx = List.fold_left (fun (ps, ctx) p ->
                let p, ctx = infer_p ctx p in p::ps, ctx) ([], ctx) ps in
            List.rev ps, ctx
        in

        let rec infer ctx : E.t -> c * t = function
        | E.Scope (ds, e) ->
            let c1, ctx = infer_decls ctx ds in
            let c2, t = infer ctx e in
            `And (c1, c2), t

        | E.Seq (l, r) ->
            let c1, _ = infer ctx l in
            let c2, t = infer ctx r in
            `And (c1, c2), t

        | E.Assign (l, r) ->
            let c1, t = infer ctx l in
            let c2, t' = infer ctx r in
            `And (c1, `And (c2, `Eq (t, t'))), t

        | E.Binop (l, r) ->
            let c1, t1 = infer ctx l in
            let c2, t2 = infer ctx r in
            `And (c1, `And (c2, `And (`Eq (t1, `Int), `Eq (t2, `Int)))), `Int

        | E.Call (f, xs) ->
            let c, t = infer ctx f in
            let cts = List.map (infer ctx) xs in
            let c = List.fold_left (fun c (c', _) -> `And (c, c')) c cts in
            let s = new_tv () in
            `And (c, `Call (t, List.map snd cts, s)), s

        | E.Subscript (x, i) ->
            let c1, t1 = infer ctx x in
            let c2, t2 = infer ctx i in
            let s = new_tv () in
            `And (c1, `And (c2, `And (`Eq (t2, `Int), `Ind (t1, s)))), s

        | E.Name x -> `Top, Context.find x ctx
        | E.Int 0 -> `Top, new_tv ()
        | E.Int _ -> `Top, `Int
        | E.String _ -> `Top, `String
        | E.Lambda (xs, b) ->
            let xts = List.map (fun x -> x, new_tv ()) xs in
            let ctx' = List.fold_left (fun ctx (x, t) -> Context.add x t ctx) ctx xts in
            let c, t = infer ctx' b in

            let c, s = simplify (ftv_context ctx) c in

            let subst_t' = subst_t (subst_map_to_fun s) IS.empty in
            let fvs = ftv_context @@ Context.map subst_t' ctx in
            let ts = List.map subst_t' @@ List.map snd xts in
            let t = subst_t' t in

            (* TODO maybe convert to de Brujne notation to simplify alpha-equality check? *)

            (*
            (* naïve approach *)
            let all_tvs = ftv IS.empty t in
            let all_tvs = ftv_c all_tvs c in
            let all_tvs = List.fold_left ftv all_tvs ts in
            Top, Arrow (IS.diff all_tvs fvs, c, ts, t)
            *)

            let signature_tvs = List.fold_left ftv (ftv IS.empty t) ts in
            let bvs, bc, fc = split_c signature_tvs fvs c in
            fc, `Arrow (bvs, bc, ts, t)

        | E.Skip -> `Top, new_tv ()
        | E.Array xs ->
            let css = List.map (infer ctx) xs in
            let t = new_tv () in
            let c = List.fold_left (fun c (c', s) -> `And (c, `And (`Eq (t, s), c'))) `Top css in
            c, `Array t

        | E.Sexp (x, xs) ->
            let css = List.map (infer ctx) xs in
            let c = List.fold_left (fun c (c', _) -> `And (c, c')) `Top css in
            let t = new_tv () in
            `And (c, `Sexp (x, t, List.map snd css)), t

        | E.If (c, t, f) ->
            let c1, _ = infer ctx c in
            let c2, t = infer ctx t in
            let c3, t' = infer ctx f in
            `And (c1, `And (c2, `And (c3, `Eq (t, t')))), t

        | E.While (c, b) ->
            let c1, _ = infer ctx c in
            let c2, _ = infer ctx b in
            `And (c1, c2), new_tv ()

        | E.DoWhile (b, c) ->
            let c1, _ = infer ctx b in
            let c2, _ = infer ctx c in
            `And (c1, c2), new_tv ()

        | E.Case (x, bs) ->
            let c, t = infer ctx x in
            let s = new_tv () in

            let f (c, ps) (p, b) =
                let p, ctx = infer_p ctx p in
                let c', s' = infer ctx b in
                `And (c, `And (c', `Eq (s, s'))), p::ps
            in

            let c, ps = List.fold_left f (c, []) bs in
            `And (c, `Match (t, List.rev ps)), s

        and infer_decl ctx = function
        | E.Var (x, v) ->
            let c, t = infer ctx v in
            `And (c, `Eq (Context.find x ctx, t))

        | E.Fun (x, xs, b) -> infer_decl ctx @@ E.Var (x, E.Lambda (xs, b))

        and infer_decls ctx ds =
            let f ctx d = Context.add (E.decl_name d) (new_tv ()) ctx in
            let ctx = List.fold_left f ctx ds in

            List.fold_left (fun c d -> `And (c, infer_decl ctx d)) `Top ds, ctx
        in

        object

            method simplify = simplify

            method pattern = infer_p
            method term = infer

            method decl = infer_decl
            method decls = infer_decls
        end
end
