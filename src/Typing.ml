
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

    (* convert all scrutinees to variables, don't erase Named patterns *)

    let case_of_variable_pass ast =
        let module M = struct

            module SS = Set.Make(String)

            let prev_idx = Stdlib.ref 0

            let rec next_var ctx =
                let idx = !prev_idx + 1 in
                prev_idx := idx ;

                let var = Printf.sprintf "var!%d" idx in

                if SS.mem var ctx
                then next_var ctx
                else var

            class pass (eval_decl, fself as _mutuals_pack) = object
                inherit [_, _, SS.t] eval_t_t_stub _mutuals_pack

                method! c_Scope ctx _ ds t =
                    let (ds, ctx) = List.fold_left (
                        fun (ds, ctx) d -> eval_decl ctx d :: ds, SS.add (decl_name d) ctx
                    ) ([], ctx) ds in

                    Scope (List.rev ds, fself ctx t)

                method! c_Case ctx _ t bs =
                    let var = next_var ctx in
                    let t = fself ctx t in

                    let process (p, b) =
                        (* Printf.eprintf "pattern: %s\n" @@ GT.show Pattern.t p ; *)

                        let bindings = Pattern.bindings p in
                        let ctx = List.fold_left (fun ctx (x, _) -> SS.add x ctx) ctx bindings in
                        let b = fself ctx b in

                        let path_to_subscript =
                            List.fold_left (fun xs i -> Subscript (xs, Int i)) (Name var)
                        in

                        let ds = List.map (fun (x, p) -> Var (x, path_to_subscript p)) bindings in

                        (* Printf.eprintf "decls: %s\n" @@ GT.show list (GT.show decl) ds ; *)

                        p, if ds = [] then b else Scope (ds, b)
                    in

                    let bs = List.map process bs in

                    Scope ([Var (var, t)], Case (Name var, bs))
            end

            let pass = let (_, f) = fix_decl eval_decl_0 (new pass) in f SS.empty
        end in

        M.pass ast
end

module Type = struct

    module IS = Set.Make(Int)
    module Context = Map.Make(String)

    type t =
    | Name      of int              (* type variable name *)
    | Int                           (* integer *)
    | String                        (* string *)
    | Arrow     of IS.t * c * t list * t (* arrow *)
    | Array     of t                (* array *)
    | Sexp      of (string * t list) list (* S-expression *)

    and c =
    | Top                           (* always true *)
    | And       of c * c            (* logical AND *)
    | Eq        of t * t            (* syntax equality *)
    | Box       of t                (* is boxed type *)
    | Fun       of t                (* is arrow *)
    | Ind       of t * t            (* indexable *)
    | IndI      of int * t * t      (* specified index *)
    | SexpC     of t                (* is sexp type *)
    | SexpX     of string * t * t list (* sexp with label and types *)
    | Call      of t * t list * t   (* callable with args and result types *)

    let show_is is = match IS.elements is with
    | i :: is -> (List.fold_left (Printf.sprintf "%s, %d") (Printf.sprintf "{%d" i) is) ^ "}"
    | [] -> "{}"

    let rec show_t = function
    | Name x -> Printf.sprintf "tv_%d" x
    | Int -> "Int"
    | String -> "String"
    | Arrow (xs, c, ts, t) -> Printf.sprintf "forall (%s). (%s) => (%s) -> %s"
        (show_is xs) (show_c c) (GT.show list show_t ts) (show_t t)
    | Array t -> Printf.sprintf "[%s]" @@ show_t t
    | Sexp vs -> "Sexp "
        ^ GT.show list (fun (x, ts) -> Printf.sprintf "%s (%s)" x @@ GT.show list show_t ts) vs

    and show_c = function
    | Top -> "T"
    | And (l, r) -> Printf.sprintf "%s && %s" (show_c l) (show_c r)
    | Eq (l, r) -> Printf.sprintf "%s = %s" (show_t l) (show_t r)
    | Box t -> Printf.sprintf "Box(%s)" @@ show_t t
    | Fun t -> Printf.sprintf "Fun(%s)" @@ show_t t
    | Ind (l, r) -> Printf.sprintf "Ind(%s, %s)" (show_t l) (show_t r)
    | IndI (i, l, r) -> Printf.sprintf "Ind_%d(%s, %s)" i (show_t l) (show_t r)
    | SexpC t -> Printf.sprintf "Sexp(%s)" @@ show_t t
    | SexpX (x, t, ts) -> Printf.sprintf "Sexp_%s(%s, %s)" x (show_t t) (GT.show list show_t ts)
    | Call (t, ts, s) -> Printf.sprintf "Call(%s, %s, %s)" (show_t t) (GT.show list show_t ts) (show_t s)

    (* free type variables *)

    let rec ftv fvs = function
    | Name x -> IS.add x fvs
    | Int -> fvs
    | String -> fvs
    | Arrow (xs, c, ts, t) ->
        let fvs = List.fold_left ftv fvs ts in
        let fvs = ftv fvs t in
        let fvs = ftv_c fvs c in
        IS.diff fvs xs
    | Array t -> ftv fvs t
    | Sexp ps -> List.fold_left (fun fvs (_, ts) -> List.fold_left ftv fvs ts) fvs ps

    and ftv_c fvs = function
    | Top -> fvs
    | And (l, r) -> ftv_c (ftv_c fvs l) r
    | Eq (l, r) -> ftv (ftv fvs l) r
    | Box t -> ftv fvs t
    | Fun t -> ftv fvs t
    | Ind (l, r) -> ftv (ftv fvs l) r
    | IndI (_, l, r) -> ftv (ftv fvs l) r
    | SexpC t -> ftv fvs t
    | SexpX (_, t, ts) -> List.fold_left ftv (ftv fvs t) ts
    | Call (t, ts, s) -> ftv (List.fold_left ftv (ftv fvs t) ts) s

    let ftv_context ctx = Context.fold (fun _ t fvs -> ftv fvs t) ctx IS.empty

    (* substitution *)

    let rec subst_t f bvs = function
    | Name x as t when IS.mem x bvs -> t
    | Name x -> f x
    | Int -> Int
    | String -> String
    | Arrow (xs, c, ts, t) ->
        let bvs = IS.union bvs xs in
        Arrow (xs, subst_c f bvs c, List.map (subst_t f bvs) ts, subst_t f bvs t)
    | Array t -> Array (subst_t f bvs t)
    | Sexp xs -> Sexp (List.map (fun (x, ts) -> x, List.map (subst_t f bvs) ts) xs)

    and subst_c f bvs = function
    | Top -> Top
    | And (l, r) -> And (subst_c f bvs l, subst_c f bvs r)
    | Eq (l, r) -> Eq (subst_t f bvs l, subst_t f bvs r)
    | Box t -> Box (subst_t f bvs t)
    | Fun t -> Fun (subst_t f bvs t)
    | Ind (l, r) -> Ind (subst_t f bvs l, subst_t f bvs r)
    | IndI (i, l, r) -> IndI (i, subst_t f bvs l, subst_t f bvs r)
    | SexpC t -> SexpC (subst_t f bvs t)
    | SexpX (x, t, ts) -> SexpX (x, subst_t f bvs t, List.map (subst_t f bvs) ts)
    | Call (t, ss, s) -> Call (subst_t f bvs t, List.map (subst_t f bvs) ss, subst_t f bvs s)

    (* trivial simplifier *)
    (* TODO simplify better *)

    let rec simplify = function
    | And (Top, x) -> simplify x
    | And (x, Top) -> simplify x
    | And (And (ll, lr), r) -> simplify @@ And (ll, And (lr, r))
    | And (l, r) -> And (simplify l, simplify r)
    | x -> x

    (* make inferrer *)

    let make_infer () =
        let module E = Expr in

        let prev_tv_idx = Stdlib.ref 0 in

        let new_tv () =
            let idx = !prev_tv_idx + 1 in
            prev_tv_idx := idx ;
            Name idx
        in

        let rec infer_pattern t = function
        | Pattern.Named (_, p) -> infer_pattern t p
        | Pattern.Wildcard -> Top, t
        | Pattern.Array ps ->
            let t1, s = new_tv (), new_tv () in
            let css = List.map (infer_pattern @@ Array t1) ps in
            let c = List.fold_left (fun c (c', s') -> And (c, And (Eq (s, s'), c'))) Top css in
            c, Array s
        | Pattern.Sexp (x, ps) ->
            let ts = List.init (List.length ps) (fun _ -> new_tv ()) in
            let css = List.map2 infer_pattern ts ps in
            let c = List.fold_left (fun c (c', _) -> And (c, c')) Top css in
            And (SexpX (x, t, ts), c), Sexp [x, List.map snd css]
        | Pattern.Const _ -> Eq (t, Int), Int
        | Pattern.String _ -> Eq (t, String), String
        | Pattern.Boxed -> Box t, t
        | Pattern.UnBoxed -> Eq (t, Int), Int
        | Pattern.StringTag -> Eq (t, String), String
        | Pattern.ArrayTag ->
            let t1 = new_tv () in
            Eq (t, Array t1), Array t1
        | Pattern.SexpTag -> SexpC t, t
        | Pattern.ClosureTag -> Fun t, t
        in

        let rec infer ctx = function
        | E.Scope (ds, e) ->
            let c1, ctx = infer_decls ctx ds in
            let c2, t = infer ctx e in
            And (c1, c2), t
        | E.Seq (l, r) ->
            let c1, _ = infer ctx l in
            let c2, t = infer ctx r in
            And (c1, c2), t
        | E.Assign (l, r) ->
            let c1, t = infer ctx l in
            let c2, t' = infer ctx r in
            And (c1, And (c2, Eq (t, t'))), t
        | E.Binop (l, r) ->
            let c1, t1 = infer ctx l in
            let c2, t2 = infer ctx r in
            And (c1, And (c2, And (Eq (t1, Int), Eq (t2, Int)))), Int
        | E.Call (f, xs) ->
            let c, t = infer ctx f in
            let cts = List.map (infer ctx) xs in
            let c = List.fold_left (fun c (c', _) -> And (c, c')) c cts in
            let s = new_tv () in
            And (c, Call (t, List.map snd cts, s)), s
        | E.Subscript (x, E.Int i) ->
            let c, t = infer ctx x in
            let s = new_tv () in
            And (c, IndI (i, t, s)), s
        | E.Subscript (x, i) ->
            let c1, t1 = infer ctx x in
            let c2, t2 = infer ctx i in
            let s = new_tv () in
            And (c1, And (c2, And (Eq (t2, Int), Ind (t1, s)))), s
        | E.Name x -> Top, Context.find x ctx
        | E.Int 0 -> Top, new_tv ()
        | E.Int _ -> Top, Int
        | E.String _ -> Top, String
        | E.Lambda (xs, b) ->
            let xts = List.map (fun x -> x, new_tv ()) xs in
            let ctx' = List.fold_left (fun ctx (x, t) -> Context.add x t ctx) ctx xts in
            let c, t = infer ctx' b in
            let c = simplify c in
            let fvs = ftv_context ctx in
            (* TODO split c by fvs? *)
            let ts = List.map snd xts in
            let all_tvs = ftv IS.empty t in
            let all_tvs = ftv_c all_tvs c in
            let all_tvs = List.fold_left ftv all_tvs ts in
            Top, Arrow (IS.diff all_tvs fvs, c, ts, t)
        | E.Skip -> Top, new_tv ()
        | E.Array xs ->
            let css = List.map (infer ctx) xs in
            let t = new_tv () in
            let c = List.fold_left (fun c (c', s) -> And (c, And (Eq (t, s), c'))) Top css in
            c, Array t
        | E.Sexp (x, xs) ->
            (* TODO weaken *)
            let css = List.map (infer ctx) xs in
            let c = List.fold_left (fun c (c', _) -> And (c, c')) Top css in
            c, Sexp [x, List.map snd css]
        | E.If (c, t, f) ->
            let c1, _ = infer ctx c in
            let c2, t = infer ctx t in
            let c3, t' = infer ctx f in
            And (c1, And (c2, And (c3, Eq (t, t')))), t
        | E.While (c, b) ->
            let c1, _ = infer ctx c in
            let c2, _ = infer ctx b in
            And (c1, c2), new_tv ()
        | E.DoWhile (b, c) ->
            let c1, _ = infer ctx b in
            let c2, _ = infer ctx c in
            And (c1, c2), new_tv ()
        | E.Case (E.Name x as x', bs) ->
            let c, t = infer ctx x' in
            let s = new_tv () in

            let f c (p, b) =
                let c1, t' = infer_pattern t p in
                let c2, s' = infer (Context.add x t' ctx) b in
                And (c, And (c1, And (Eq (s, s'), c2)))
            in

            List.fold_left f c bs, s
        | E.Case _ -> invalid_arg "Case of complex term"

        and infer_decl ctx = function
        | E.Var (x, v) ->
            let c, t = infer ctx v in
            And (c, Eq (Context.find x ctx, t))
        | E.Fun (x, xs, b) -> infer_decl ctx @@ E.Var (x, E.Lambda (xs, b))

        and infer_decls ctx ds =
            let f ctx d = Context.add (E.decl_name d) (new_tv ()) ctx in
            let ctx = List.fold_left f ctx ds in

            List.fold_left (fun c d -> And (c, infer_decl ctx d)) Top ds, ctx
        in

        object

            method pattern = infer_pattern
            method term = infer

            method decl = infer_decl
            method decls = infer_decls
        end
end
