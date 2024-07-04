
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

    module SexpLabel = struct

        type t = string * int

        let compare (l, n) (k, m) =
            let x = String.compare l k in
            if x <> 0 then x else Int.compare n m
    end

    module SexpConstructors = Map.Make(SexpLabel)

    type t = [
    | `GVar     of int              (* ground type variable *)
    | `LVar     of int * int        (* logic type variable *)
    | `Int                          (* integer *)
    | `String                       (* string *)
    | `Array    of t                (* array *)
    | `Sexp     of sexp             (* S-expression *)
    | `Arrow    of IS.t * c list * t list * t (* arrow *)
    | `Mu       of int * t          (* mu-type *)
    ]

    and sexp = t list SexpConstructors.t * int

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
    | `Eq       of t * t            (* syntax equality *)
    | `Ind      of t * t            (* indexable *)
    | `Call     of t * t list * t   (* callable with args and result types *)
    | `Match    of t * p list       (* match type with patterns *)
    ]

    let show_is is = match IS.elements is with
    | i :: is -> (List.fold_left (Printf.sprintf "%s, %d") (Printf.sprintf "{%d" i) is) ^ "}"
    | [] -> "{}"

    let rec show_t : t -> _ = function
    | `GVar x -> Printf.sprintf "gv_%d" x
    | `LVar (x, l) -> Printf.sprintf "lv_%d^%d" x l
    | `Int -> "Int"
    | `String -> "String"
    | `Array t -> Printf.sprintf "[%s]" @@ show_t t
    | `Sexp xs -> show_sexp xs
    | `Arrow (xs, c, ts, t) -> Printf.sprintf "forall %s. %s => %s -> %s"
        (show_is xs) (GT.show list show_c c) (GT.show list show_t ts) (show_t t)

    | `Mu (x, t) -> Printf.sprintf "mu %d. %s" x @@ show_t t

    and show_sexp ((xs, row) : sexp) = match List.of_seq @@ SexpConstructors.to_seq xs with
    | (_ :: _) as xs -> (String.concat " \\/ " @@ List.map
        (fun ((l, _), ts) -> Printf.sprintf "%s %s" l (GT.show list show_t ts)) xs)
        ^ Printf.sprintf " \\/ row_%d" row
    | [] -> Printf.sprintf "row_%d" row

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
    | `Eq (l, r) -> Printf.sprintf "%s = %s" (show_t l) (show_t r)
    | `Ind (l, r) -> Printf.sprintf "Ind(%s, %s)" (show_t l) (show_t r)
    | `Call (t, ts, s) -> Printf.sprintf "Call(%s, %s, %s)" (show_t t) (GT.show list show_t ts) (show_t s)
    | `Match (t, ps) -> Printf.sprintf "Match(%s, %s)" (show_t t) (GT.show list show_p ps)

    (* free logic type variables *)

    let free_lvars p =
        let rec ftv_t bvs fvs : t -> _ = function
        | `GVar x ->
            if not @@ IS.mem x bvs then failwith "free_lvars: free ground variable" ;
            fvs

        | `LVar (x, l) ->
            if IS.mem x bvs then failwith "free_lvars: bound logic variable" ;
            if p l then IS.add x fvs else fvs

        | `Int -> fvs
        | `String -> fvs
        | `Array t -> ftv_t bvs fvs t
        | `Sexp xs -> ftv_sexp bvs fvs xs

        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            ftv_t bvs (List.fold_left (ftv_t bvs) (List.fold_left (ftv_c bvs) fvs c) ts) t

        | `Mu (x, t) -> ftv_t (IS.add x bvs) fvs t

        and ftv_sexp bvs fvs ((xs, _) : sexp) =
            SexpConstructors.fold (fun _ ts fvs -> List.fold_left (ftv_t bvs) fvs ts) xs fvs

        and ftv_p bvs fvs : p -> _ = function
        | `Wildcard -> fvs
        | `Typed (t, p) -> ftv_p bvs (ftv_t bvs fvs t) p
        | `Array ps -> List.fold_left (ftv_p bvs) fvs ps
        | `Sexp (_, ps) -> List.fold_left (ftv_p bvs) fvs ps
        | `Boxed -> fvs
        | `Unboxed -> fvs
        | `StringTag -> fvs
        | `ArrayTag -> fvs
        | `SexpTag -> fvs
        | `FunTag -> fvs

        and ftv_c bvs fvs : c -> _ = function
        | `Eq (l, r) -> ftv_t bvs (ftv_t bvs fvs l) r
        | `Ind (l, r) -> ftv_t bvs (ftv_t bvs fvs l) r
        | `Call (t, ts, t') -> ftv_t bvs (List.fold_left (ftv_t bvs) (ftv_t bvs fvs t) ts) t'
        | `Match (t, ps) -> List.fold_left (ftv_p bvs) (ftv_t bvs fvs t) ps
        in

        object

            method t = ftv_t
            method sexp = ftv_sexp
            method p = ftv_p
            method c = ftv_c
        end

    (* convert logic variables to ground *)

    let lvars_to_gvars p =
        let rec ltog_t bvs : t -> t = function
        | `GVar x as t ->
            if not @@ IS.mem x bvs then failwith "free_lvars: free ground variable" ;
            t

        | `LVar (x, l) as t ->
            if IS.mem x bvs then failwith "free_lvars: bound logic variable" ;
            if p l then `GVar x else t

        | `Int -> `Int
        | `String -> `String
        | `Array t -> `Array (ltog_t bvs t)
        | `Sexp xs -> `Sexp (ltog_sexp bvs xs)
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            `Arrow (xs, List.map (ltog_c bvs) c, List.map (ltog_t bvs) ts, ltog_t bvs t)

        | `Mu (x, t) -> `Mu (x, ltog_t bvs t)

        and ltog_sexp bvs ((xs, row) : sexp) : sexp =
            (SexpConstructors.map (List.map @@ ltog_t bvs) xs, row)

        and ltog_p bvs : p -> p = function
        | `Wildcard -> `Wildcard
        | `Typed (t, p) -> `Typed (ltog_t bvs t, ltog_p bvs p)
        | `Array ps -> `Array (List.map (ltog_p bvs) ps)
        | `Sexp (x, ps) -> `Sexp (x, List.map (ltog_p bvs) ps)
        | `Boxed -> `Boxed
        | `Unboxed -> `Unboxed
        | `StringTag -> `StringTag
        | `ArrayTag -> `ArrayTag
        | `SexpTag -> `SexpTag
        | `FunTag -> `FunTag

        and ltog_c bvs : c -> c = function
        | `Eq (t1, t2) -> `Eq (ltog_t bvs t1, ltog_t bvs t2)
        | `Ind (t1, t2) -> `Ind (ltog_t bvs t1, ltog_t bvs t2)
        | `Call (t, ts, t') -> `Call (ltog_t bvs t, List.map (ltog_t bvs) ts, ltog_t bvs t')
        | `Match (t, ps) -> `Match (ltog_t bvs t, List.map (ltog_p bvs) ps)
        in

        object

            method t = ltog_t
            method sexp = ltog_sexp
            method p = ltog_p
            method c = ltog_c
        end

    (* substitution *)

    module Subst = struct

        type value
        = Type of t
        | Sexp of sexp

        include Subst.Make(struct type t = value end)

        let unpack_type = function
        | Type t -> t
        | _ -> failwith "unpack_type: not a type variable"

        let unpack_sexp = function
        | Sexp t -> t
        | _ -> failwith "unpack_type: not a row variable"

        let find_type x s = Option.map unpack_type @@ find x s
        let find_sexp x s = Option.map unpack_sexp @@ find x s

        let bind_type v t = bind_term v @@ Type t
        let bind_sexp v t = bind_term v @@ Sexp t
    end

    let apply_subst s =
        let module IM = Map.Make(Int) in

        let vars_path = Stdlib.ref IM.empty in

        let rec subst_t bvs : t -> t = function
        | `GVar x as t ->
            if not @@ IS.mem x bvs then failwith "apply_subst: free ground variable" ;
            t

        | `LVar (x, _) as t ->
            if IS.mem x bvs then failwith "apply_subst: bound logic variable" ;

            let old_vars_path = !vars_path in

            if IM.mem x old_vars_path
            then begin
                (* variable `x` is recursive *)
                vars_path := IM.add x true old_vars_path ;
                `GVar x

            end else begin
                match Subst.find_type x s with
                | None -> t
                | Some t ->
                    vars_path := IM.add x false old_vars_path ;

                    let res = subst_t bvs t in

                    let new_vars_path = !vars_path in
                    vars_path := IM.remove x new_vars_path ;

                    (* check is `x` become recursive *)
                    if IM.find x new_vars_path
                    then `Mu (x, res)
                    else res
            end

        | `Int -> `Int
        | `String -> `String
        | `Array t -> `Array (subst_t bvs t)
        | `Sexp xs -> `Sexp (subst_sexp bvs xs)
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            `Arrow (xs, List.map (subst_c bvs) c, List.map (subst_t bvs) ts, subst_t bvs t)

        | `Mu (x, t) -> `Mu (x, subst_t (IS.add x bvs) t)

        and subst_sexp bvs (xs, row) =
            let xs = SexpConstructors.map (List.map @@ subst_t bvs) xs in

            match Subst.find_sexp row s with
            | None -> xs, row
            | Some (xs', row') -> 
                let f _ _ _ = failwith "subst_sexp: intersecting constructors" in
                let xs = SexpConstructors.union f xs xs' in

                subst_sexp bvs (xs, row')

        and subst_p bvs : p -> p = function
        | `Wildcard -> `Wildcard
        | `Typed (t, p) -> `Typed (subst_t bvs t, subst_p bvs p)
        | `Array ps -> `Array (List.map (subst_p bvs) ps)
        | `Sexp (x, ps) -> `Sexp (x, List.map (subst_p bvs) ps)
        | `Boxed -> `Boxed
        | `Unboxed -> `Unboxed
        | `StringTag -> `StringTag
        | `ArrayTag -> `ArrayTag
        | `SexpTag -> `SexpTag
        | `FunTag -> `FunTag

        and subst_c bvs : c -> c = function
        | `Eq (t1, t2) -> `Eq (subst_t bvs t1, subst_t bvs t2)
        | `Ind (t1, t2) -> `Ind (subst_t bvs t1, subst_t bvs t2)
        | `Call (t, ts, t') -> `Call (subst_t bvs t, List.map (subst_t bvs) ts, subst_t bvs t')
        | `Match (t, ps) -> `Match (subst_t bvs t, List.map (subst_p bvs) ps)
        in

        object

            method t = subst_t
            method sexp = subst_sexp
            method p = subst_p
            method c = subst_c
        end

    exception Unification_failure of t * t

    (* unification, returns substitution and residual equations *)

    let unify var_gen level =
        let new_var () =
            let idx = !var_gen + 1 in
            var_gen := idx ;

            idx
        in

        let module Mut = struct

            type x = Subst.t * (t * t) list
            type t = x -> x
        end in

        let rec unify_t : t * t -> Mut.t = function

        (* === lowlevel var vs lowlevel var === *)

        | `LVar (x, l), `LVar (y, k) when l >= level && k >= level ->
            fun (s, r) -> begin
                try Subst.bind_vars x y s, r
                with Subst.Need_unification (t1, t2) ->
                    unify_t (Subst.unpack_type t1, Subst.unpack_type t2) (s, r)
            end

        (* === lowlevel var vs term === *)

        | `LVar (x, l), t when l >= level ->
            fun (s, r) -> begin
                try Subst.bind_type x t s, r
                with Subst.Need_unification (t1, t2) ->
                    unify_t (Subst.unpack_type t1, Subst.unpack_type t2) (s, r)
            end

        | t1, (`LVar (_, l) as t2) when l >= level -> unify_t (t2, t1)

        (* === highlevel vars === *)

        | `LVar (x, l), `LVar (y, k) when x = y ->
            if l <> k then failwith "unify: same variable on different levels" ;
            Fun.id

        | `LVar (_, l) as t1, (`LVar (_, k) as t2) when l > k -> unify_t (t2, t1)
        | `LVar (x, l), t ->
            (*  example: lv_1^0 = [lv_2^1]
             *  result:  lv_1^0 = [lv_3^0] and lv_2^1 |-> lv_3^0
             *
             *  we need to <<refresh>> lowlevel variables in type `t` with highlevel ones
             *  and record refreshing in result substitution (lv_2^1 |-> lv_3^0),
             *  as a residual we record refreshed equation (lv_1^0 = [lv_3^0])
             *
             *  !!! same operation we need to do with all constraints below !!!
             *)

            failwith "TODO: deal with lowlevel variables in t"

        | t1, (`LVar (_, _) as t2) -> unify_t (t2, t1)

        (* === term vs term === *)

        | `GVar x, `GVar y when x = y -> Fun.id
        | `Int, `Int -> Fun.id
        | `String, `String -> Fun.id
        | `Array t1, `Array t2 -> unify_t (t1, t2)
        | `Sexp xs1, `Sexp xs2 -> unify_sexp (xs1, xs2)
        | `Arrow (xs1, c1, ts1, t1), `Arrow (xs2, c2, ts2, t2) -> failwith "TODO: unify arrows"
        | `Mu (x1, t1), `Mu (x2, t2) -> failwith "TODO: unify recursive types"
        | t1, t2 -> raise @@ Unification_failure (t1, t2)

        and unify_sexp ((xs1, row1), (xs2, row2)) : Mut.t =
            let xs1'empty = SexpConstructors.is_empty xs1 in
            let xs2'empty = SexpConstructors.is_empty xs2 in

            if xs1'empty && xs2'empty then begin fun (s, r) ->
                try Subst.bind_vars row1 row2 s, r
                with Subst.Need_unification (t1, t2) ->
                    unify_sexp (Subst.unpack_sexp t1, Subst.unpack_sexp t2) (s, r)

            end else if xs1'empty then begin fun (s, r) ->
                try Subst.bind_sexp row1 (xs2, row2) s, r
                with Subst.Need_unification (t1, t2) ->
                    unify_sexp (Subst.unpack_sexp t1, Subst.unpack_sexp t2) (s, r)

            end else if xs2'empty then begin
                unify_sexp ((xs2, row2), (xs1, row1))

            end else begin
                let module SLS = Set.Make(SexpLabel) in

                let fst (l, _) = l in
                let xs1'labels = SLS.of_seq @@ Seq.map fst @@ SexpConstructors.to_seq xs1 in
                let xs2'labels = SLS.of_seq @@ Seq.map fst @@ SexpConstructors.to_seq xs2 in

                let both_f' x s =
                    let ts1 = SexpConstructors.find x xs1 in
                    let ts2 = SexpConstructors.find x xs2 in

                    List.fold_left2 (fun s t1 t2 -> unify_t (t1, t2) s) s ts1 ts2
                in

                let both = SLS.inter xs1'labels xs2'labels in
                let both_f = SLS.fold both_f' both in

                let xs1_only = SLS.fold SexpConstructors.remove both xs1 in
                let xs2_only = SLS.fold SexpConstructors.remove both xs2 in

                let xs1_only'empty = SexpConstructors.is_empty xs1_only in
                let xs2_only'empty = SexpConstructors.is_empty xs2_only in

                if not xs1_only'empty && not xs2_only'empty then begin
                    let row = new_var () in

                    let row1_f = unify_sexp ((SexpConstructors.empty, row1), (xs2_only, row)) in
                    let row2_f = unify_sexp ((SexpConstructors.empty, row2), (xs1_only, row)) in

                    fun s -> row2_f @@ row1_f @@ both_f s

                end else begin
                    let only_f = unify_sexp ((xs1_only, row1), (xs2_only, row2)) in
                    fun s -> only_f @@ both_f s
                end
            end
        in

        object

            method t = unify_t
            method sexp = unify_sexp
        end

    (* constraints simplifier *)

    module Simpl = struct

        type st = {

            s: Subst.t;
            r: c list;
        }

        type fail =
        | Nested of fail list
        | Unification of t * t

        exception Failure of fail
    end

    let simplify var_gen level =
        let open Simpl in

        let unify = unify var_gen level in

        let single_step deterministic st : c -> (c list * st) list = function
        | `Eq (t1, t2) -> begin try
            let s, r = unify#t (t1, t2) (st.s, []) in

            let r = List.map (fun (t1, t2) -> `Eq (t1, t2)) r in
            [[], { s = s; r = r @ st.r }]

            with Unification_failure (t1, t2) -> raise @@ Failure (Unification (t1, t2))
            end

        | c -> failwith @@ "TODO " ^ show_c c
        in

        let one_step deterministic st =
            let rec hlp cs' : c list -> (c list * st) list = function
            | [] -> []
            | c :: cs ->
                let xs = single_step deterministic st c in

                if xs = []
                then hlp (c :: cs') cs
                else List.map (fun (new_cs, st) -> List.rev cs' @ new_cs @ cs, st) xs
            in

            hlp []
        in

        let one_step ?(deterministic=false) cs st = one_step deterministic st cs in

        let rec full_deterministic cs st : c list * st =
            match one_step ~deterministic:true cs st with
            | [] -> cs, st
            | [cs, st] -> full_deterministic cs st
            | _ -> failwith "BUG: non-deterministic solution"
        in

        let rec full cs st : st =
            let cs, st = full_deterministic cs st in
            if cs = [] then st else full' [] @@ one_step cs st

        and full' errs = function
        | [] ->
            if errs = [] then failwith "BUG: no solutions" ;
            raise @@ Failure (Nested errs)

        | (cs, st) :: xs ->
            try full cs st
            with Failure err -> full' (err :: errs) xs
        in

        object

            method full_deterministic = full_deterministic
            method full = full

            method run : 'a. ?s : Subst.t -> (st -> 'a) -> 'a =
                fun ?(s=Subst.empty) f -> f { s = s; r = [] }
        end

    (* type inferrer *)

    let infer () =
        let module E = Expr in

        let prev_var_idx = Stdlib.ref 0 in
        let current_level = Stdlib.ref 0 in

        let new_var () =
            let idx = !prev_var_idx + 1 in
            prev_var_idx := idx ;
            idx
        in

        let new_tv () = `LVar (new_var (), !current_level) in

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

        let rec infer_t ctx : E.t -> c list * t = function
        | E.Scope (ds, e) ->
            let c1, ctx = infer_decls ctx ds in
            let c2, t = infer_t ctx e in
            c1 @ c2, t

        | E.Seq (l, r) ->
            let c1, _ = infer_t ctx l in
            let c2, t = infer_t ctx r in
            c1 @ c2, t

        | E.Assign (l, r) ->
            let c1, t = infer_t ctx l in
            let c2, t' = infer_t ctx r in
            `Eq (t, t') :: c1 @ c2, t

        | E.Binop (l, r) ->
            let c1, t1 = infer_t ctx l in
            let c2, t2 = infer_t ctx r in
            `Eq (t1, `Int) :: `Eq (t2, `Int) :: c1 @ c2, `Int

        | E.Call (f, xs) ->
            let c, t = infer_t ctx f in
            let cts = List.map (infer_t ctx) xs in
            let c = List.fold_left (fun c (c', _) -> c @ c') c cts in
            let s = new_tv () in
            `Call (t, List.map snd cts, s) :: c, s

        | E.Subscript (x, i) ->
            let c1, t1 = infer_t ctx x in
            let c2, t2 = infer_t ctx i in
            let s = new_tv () in
            `Eq (t2, `Int) :: `Ind (t1, s) :: c1 @ c2, s

        | E.Name x -> [], Context.find x ctx
        | E.Int 0 -> [], new_tv ()
        | E.Int _ -> [], `Int
        | E.String _ -> [], `String
        | E.Lambda (xs, b) ->
            (* here we generate variables for parameters on special level `k` *)

            current_level := !current_level + 1 ;

            let xts = List.map (fun x -> x, new_tv ()) xs in

            (* next we infer_t type of body on lower level (`k + 1`)
             * and simplify them on this level
             *)

            current_level := !current_level + 1 ;

            let ctx' = List.fold_left (fun ctx (x, t) -> Context.add x t ctx) ctx xts in
            let c, t = infer_t ctx' b in

            let Simpl.{ s; r = c } =
                let simplify = simplify prev_var_idx !current_level in
                simplify#run @@ simplify#full c
            in

            (* after that we have residual constraints and substitution
             *
             * we perform deterministic simplification on level `k`
             * to eliminate obvious constraints
             *
             * note that if we do non-deterministic simplification here,
             * we will get overspecialized solution
             *)

            current_level := !current_level - 1 ;

            let bc, Simpl.{ s; r = fc } =
                let simplify = simplify prev_var_idx !current_level in
                simplify#run ~s @@ simplify#full_deterministic c
            in

            (* now we have two kinds of residual constraints:
             * "true" residual constraints are free since we unable to solve them on level `k`,
             * other returned constraints are bound since we unable to solve them deterministically
             *
             * we apply substitution and collect free variables on level `k` and `k + 1` as bound
             *)

            let apply_subst = apply_subst s in
            let ts = List.map (fun (_, t) -> apply_subst#t IS.empty t) xts in
            let bc = List.map (apply_subst#c IS.empty) bc in
            let t = apply_subst#t IS.empty t in

            let bvs =
                let level = !current_level in
                let free_lvars = free_lvars @@ fun l -> l >= level in

                let fvs = IS.empty in
                let fvs = List.fold_left (free_lvars#t IS.empty) fvs ts in
                let fvs = List.fold_left (free_lvars#c IS.empty) fvs bc in
                let fvs = free_lvars#t IS.empty fvs t in
                fvs
            in

            (* to build result type, we need to convert bound variables to ground *)

            let bc, ts, t =
                let level = !current_level in
                let lvars_to_gvars = lvars_to_gvars @@ fun l -> l >= level in

                let ts = List.map (lvars_to_gvars#t IS.empty) ts in
                let bc = List.map (lvars_to_gvars#c IS.empty) bc in
                let t = lvars_to_gvars#t IS.empty t in
                bc, ts, t
            in

            fc, `Arrow (bvs, bc, ts, t)

        | E.Skip -> [], new_tv ()
        | E.Array xs ->
            let css = List.map (infer_t ctx) xs in
            let t = new_tv () in
            let c = List.fold_left (fun c (c', s) -> `Eq (t, s) :: c @ c') [] css in
            c, `Array t

        | E.Sexp (x, xs) ->
            let css = List.map (infer_t ctx) xs in
            let c = List.fold_left (fun c (c', _) -> c @ c') [] css in

            let t = new_tv () in
            let xs = SexpConstructors.singleton (x, List.length xs) @@ List.map snd css in
            `Eq (t, `Sexp (xs, new_var ())) :: c, t

        | E.If (c, t, f) ->
            let c1, _ = infer_t ctx c in
            let c2, t = infer_t ctx t in
            let c3, t' = infer_t ctx f in
            `Eq (t, t') :: c1 @ c2 @ c3, t

        | E.While (c, b) ->
            let c1, _ = infer_t ctx c in
            let c2, _ = infer_t ctx b in
            c1 @ c2, new_tv ()

        | E.DoWhile (b, c) ->
            let c1, _ = infer_t ctx b in
            let c2, _ = infer_t ctx c in
            c1 @ c2, new_tv ()

        | E.Case (x, bs) ->
            let c, t = infer_t ctx x in
            let s = new_tv () in

            let f (c, ps) (p, b) =
                let p, ctx = infer_p ctx p in
                let c', s' = infer_t ctx b in
                `Eq (s, s') :: c @ c', p::ps
            in

            let c, ps = List.fold_left f (c, []) bs in
            `Match (t, List.rev ps) :: c, s

        and infer_decl ctx = function
        | E.Var (x, v) ->
            let c, t = infer_t ctx v in
            `Eq (Context.find x ctx, t) :: c

        | E.Fun (x, xs, b) -> infer_decl ctx @@ E.Var (x, E.Lambda (xs, b))

        and infer_decls ctx ds =
            let f ctx d = Context.add (E.decl_name d) (new_tv ()) ctx in
            let ctx = List.fold_left f ctx ds in

            List.fold_left (fun c d -> infer_decl ctx d @ c) [] ds, ctx
        in

        object

            method pattern = infer_p
            method term = infer_t

            method decl = infer_decl
            method decls = infer_decls

            method simplify = simplify prev_var_idx
        end
end
