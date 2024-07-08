
module Pattern = Language.Pattern

module Expr = struct

    type decl_info = {

        public : bool;
        name : string;
    }

    type position = {

        row : int;
        col : int;
    }

    type expr_info = {

        name : string;
        pos : position;
    }

    type expr_form =
    | Scope     of decl list * expr     (* scope expression *)
    | Seq       of expr * expr          (* sequence point *)
    | Assign    of expr * expr          (* assignment *)
    | Binop     of expr * expr          (* binary operator *)
    | Call      of expr * expr list     (* call *)
    | Subscript of expr * expr          (* subscript *)
    | Name      of string               (* variable name *)
    | Int       of int                  (* integer *)
    | String    of string               (* string *)
    | Lambda    of string list * expr   (* lambda expression *)
    | Skip                              (* skip *)
    | Array     of expr list            (* array *)
    | Sexp      of string * expr list   (* S-expression *)
    | If        of expr * expr * expr   (* if-then-else *)
    | While     of expr * expr          (* while loop *)
    | DoWhile   of expr * expr          (* do-while loop *)
    | Case      of expr * (Pattern.t * expr) list (* case-of *)

    and expr = expr_form * expr_info

    and decl_form =
    | Var of expr
    | Fun of string list * expr

    and decl = decl_form * decl_info

    let is_public = function
    | `Public | `PublicExtern -> true
    | _ -> false

    module L = Language.Expr

    let rec from_language name e =
        let return form = form, { name ; pos = { row = 0 ; col = 0 } } in

        match e with
        | L.Const x -> return @@ Int x
        | L.Array xs -> return @@ Array (List.map (from_language name) xs)
        | L.String x -> return @@ String x
        | L.Sexp (x, xs) -> return @@ Sexp (x, List.map (from_language name) xs)
        | L.Var x -> return @@ Name x
        | L.Ref x -> return @@ Name x
        | L.Binop (_, l, r) -> return @@ Binop (from_language name l, from_language name r)
        | L.Elem (xs, i) -> return @@ Subscript (from_language name xs, from_language name i)
        | L.ElemRef (xs, i) -> return @@ Subscript (from_language name xs, from_language name i)
        | L.Call (f, xs) -> return @@ Call (from_language name f, List.map (from_language name) xs)
        | L.Assign (l, r) -> return @@ Assign (from_language name l, from_language name r)
        | L.Seq (l, r) -> return @@ Seq (from_language name l, from_language name r)
        | L.Skip -> return @@ Skip
        | L.If (c, t, f) -> return @@ If (from_language name c, from_language name t, from_language name f)
        | L.While (c, b) -> return @@ While (from_language name c, from_language name b)
        | L.DoWhile (b, c) -> return @@ DoWhile (from_language name b, from_language name c)
        | L.Case (x, bs, _, _) ->
            let f (p, b) = p, from_language name b in
            return @@ Case (from_language name x, List.map f bs)

        | L.Ignore t -> from_language name t
        | L.Unit -> return @@ Int 0
        | L.Scope (ds, t) -> return @@ Scope (List.map decl_from_language ds, from_language name t)
        | L.Lambda (xs, b) -> return @@ Lambda (xs, from_language name b)
        | L.Leave -> invalid_arg "Leave"
        | L.Intrinsic _ -> invalid_arg "Intrinsic"
        | L.Control _ -> invalid_arg "Control"

    and decl_from_language (name, (q, d)) =
        let inf = { public = is_public q ; name } in

        match d with
        | `Fun      (xs,  t) -> Fun (xs, from_language name t), inf
        | `Variable  None    -> Var (Int 0, { name; pos = { row = 0 ; col = 0 } }), inf
        | `Variable (Some t) -> Var (from_language name t), inf
end

module Type = struct

    module IS = Set.Make(Int)
    module IM = Map.Make(Int)
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

    and sexp = t list SexpConstructors.t * int option

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
    | `Sexp     of string * t * t list (* type is S-expression *)
    ]

    type c_info = {

        path : string list;
        pos : Expr.position;

        parents : c list;
    }

    type c_aux = c * c_info

    let show_is is =
        let is = IS.elements is in
        let is = String.concat ", " @@ List.map string_of_int is in
        "{" ^ is ^ "}"

    let show_list f xs = String.concat ", " @@ List.map f xs

    let rec show_t : t -> _ = function
    | `GVar x -> Printf.sprintf "gv_%d" x
    | `LVar (x, l) -> Printf.sprintf "lv_%d^%d" x l
    | `Int -> "Int"
    | `String -> "String"
    | `Array t -> Printf.sprintf "[%s]" @@ show_t t
    | `Sexp xs -> show_sexp xs
    | `Arrow (xs, c, ts, t) -> Printf.sprintf "forall %s. (%s) => (%s) -> %s"
        (show_is xs) (show_list show_c c) (show_list show_t ts) (show_t t)

    | `Mu (x, t) -> Printf.sprintf "mu %d. %s" x @@ show_t t

    and show_sexp ((xs, row) : sexp) =
        let f ((l, _), ts) = Printf.sprintf "%s (%s)" l @@ show_list show_t ts in

        let xs = List.map f @@ List.of_seq @@ SexpConstructors.to_seq xs in
        let row = Option.to_list @@ Option.map (Printf.sprintf "row_%d") row in

        String.concat " \\/ " @@ xs @ row

    and show_p : p -> _ = function
    | `Wildcard -> "_"
    | `Typed (t, p) -> Printf.sprintf "%s @ %s" (show_t t) (show_p p)
    | `Array ps -> "[" ^ show_list show_p ps ^ "]"
    | `Sexp (x, ps) -> Printf.sprintf "%s (%s)" x @@ show_list show_p ps
    | `Boxed -> "#box"
    | `Unboxed -> "#val"
    | `StringTag -> "#str"
    | `ArrayTag -> "#array"
    | `SexpTag -> "#sexp"
    | `FunTag -> "#fun"

    and show_c : c -> _ = function
    | `Eq (l, r) -> Printf.sprintf "%s = %s" (show_t l) (show_t r)
    | `Ind (l, r) -> Printf.sprintf "Ind(%s, %s)" (show_t l) (show_t r)
    | `Call (t, ts, s) -> Printf.sprintf "Call(%s, %s)" (show_list show_t @@ t :: ts) (show_t s)
    | `Match (t, ps) -> Printf.sprintf "Match(%s, %s)" (show_t t) (show_list show_p ps)
    | `Sexp (x, t, ts) -> Printf.sprintf "Sexp_%s(%s)" x (show_list show_t @@ t :: ts)

    (* logic type variables with no respect to substitution *)

    let lvars p =
        let rec ftv_t bvs fvs : t -> _ = function
        | `GVar x ->
            if not @@ IS.mem x bvs then failwith "lvars: free ground variable" ;
            fvs

        | `LVar (x, l) ->
            if IS.mem x bvs then failwith "lvars: bound logic variable" ;
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
        | `Sexp (_, t, ts) -> List.fold_left (ftv_t bvs) (ftv_t bvs fvs t) ts
        in

        object

            method t = ftv_t
            method sexp = ftv_sexp
            method p = ftv_p
            method c = ftv_c
        end

    (* convert logic variables to ground with no respect to substitution *)

    let lvars_to_gvars p =
        let rec ltog_t bvs : t -> t = function
        | `GVar x as t ->
            if not @@ IS.mem x bvs then failwith "lvars_to_gvars: free ground variable" ;
            t

        | `LVar (x, l) as t ->
            if IS.mem x bvs then failwith "lvars_to_gvars: bound logic variable" ;
            if p l then `GVar x else t

        | `Int -> `Int
        | `String -> `String
        | `Array t -> `Array (ltog_t bvs t)
        | `Sexp xs -> `Sexp (ltog_sexp bvs xs)
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            `Arrow (xs, List.map (ltog_c bvs) c, List.map (ltog_t bvs) ts, ltog_t bvs t)

        | `Mu (x, t) -> `Mu (x, ltog_t (IS.add x bvs) t)

        and ltog_sexp bvs ((xs, row) : sexp) : sexp =
            SexpConstructors.map (List.map @@ ltog_t bvs) xs, row

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
        | `Sexp (x, t, ts) -> `Sexp (x, ltog_t bvs t, List.map (ltog_t bvs) ts)
        in

        object

            method t = ltog_t
            method sexp = ltog_sexp
            method p = ltog_p
            method c = ltog_c
        end

    (* refresh ground variables with logic with no respect to substitution *)

    let gvars_to_lvars level xs =
        let rec gtol_t bvs = function
        | `GVar x as t ->
            begin match IM.find_opt x xs with
            | Some x -> `LVar (x, level)
            | None ->
                if not @@ IS.mem x bvs then failwith "gvars_to_lvars: free ground variable" ;
                t
            end

        | `LVar (_, l) as t ->
            if l >= level then failwith "gvars_to_lvars: logic variable occurred" ;
            t

        | `Int -> `Int
        | `String -> `String
        | `Array t -> `Array (gtol_t bvs t)
        | `Sexp xs -> `Sexp (gtol_sexp bvs xs)
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            `Arrow (xs, List.map (gtol_c bvs) c, List.map (gtol_t bvs) ts, gtol_t bvs t)

        | `Mu (x, t) -> `Mu (x, gtol_t (IS.add x bvs) t)

        and gtol_sexp bvs ((xs, row) : sexp) : sexp =
            SexpConstructors.map (List.map @@ gtol_t bvs) xs, row

        and gtol_p bvs : p -> p = function
        | `Wildcard -> `Wildcard
        | `Typed (t, p) -> `Typed (gtol_t bvs t, gtol_p bvs p)
        | `Array ps -> `Array (List.map (gtol_p bvs) ps)
        | `Sexp (x, ps) -> `Sexp (x, List.map (gtol_p bvs) ps)
        | `Boxed -> `Boxed
        | `Unboxed -> `Unboxed
        | `StringTag -> `StringTag
        | `ArrayTag -> `ArrayTag
        | `SexpTag -> `SexpTag
        | `FunTag -> `FunTag

        and gtol_c bvs : c -> c = function
        | `Eq (t1, t2) -> `Eq (gtol_t bvs t1, gtol_t bvs t2)
        | `Ind (t1, t2) -> `Ind (gtol_t bvs t1, gtol_t bvs t2)
        | `Call (t, ts, t') -> `Call (gtol_t bvs t, List.map (gtol_t bvs) ts, gtol_t bvs t')
        | `Match (t, ps) -> `Match (gtol_t bvs t, List.map (gtol_p bvs) ps)
        | `Sexp (x, t, ts) -> `Sexp (x, gtol_t bvs t, List.map (gtol_t bvs) ts)
        in

        object

            method t = gtol_t
            method sexp = gtol_sexp
            method p = gtol_p
            method c = gtol_c
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
        | _ -> failwith "unpack_sexp: not a row variable"

        let find_type x s = Option.map unpack_type @@ find x s
        let find_sexp x s = Option.map unpack_sexp @@ find x s

        let bind_type v t = bind_term v @@ Type t
        let bind_sexp v t = bind_term v @@ Sexp t
    end

    let apply_subst s =
        let vars_path = Stdlib.ref IM.empty in

        let rec subst_t bvs : t -> t = function
        | `GVar x as t ->
            if not @@ IS.mem x bvs then failwith "apply_subst: free ground variable" ;
            t

        | `LVar (x, l) ->
            if IS.mem x bvs then failwith "apply_subst: bound logic variable" ;

            let old_vars_path = !vars_path in

            if IM.mem x old_vars_path then begin
                (* variable `x` is recursive *)
                vars_path := IM.add x true old_vars_path ;
                `GVar x

            end else begin
                match Subst.find_type x s with
                | None ->
                    (* here level may be wrong if substitution applied on several levels! *)
                    `LVar (Subst.find_var x s, l)

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

            match Option.bind row @@ fun row -> Subst.find_sexp row s with
            | None -> xs, row
            | Some (xs', row') ->
                let f _ _ _ = failwith "apply_subst: intersecting constructors in S-exp" in
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
        | `Sexp (x, t, ts) -> `Sexp (x, subst_t bvs t, List.map (subst_t bvs) ts)
        in

        object

            method t = subst_t
            method sexp = subst_sexp
            method p = subst_p
            method c = subst_c
        end

    (* lift unbound logic variables from lower levels to `k` *)

    let lift_lvars var_gen level =
        let new_var () =
            let idx = !var_gen + 1 in
            var_gen := idx ;

            idx
        in

        let module Mut = struct

            type t = Subst.t -> Subst.t
        end in

        let rec lift_t bvs : t -> Mut.t = function
        | `GVar x ->
            if not @@ IS.mem x bvs then failwith "lift_lvars: free ground variable" ;
            Fun.id

        | `LVar (x, l) ->
            if IS.mem x bvs then failwith "lift_lvars: bound logic variable" ;

            if l <= level then Fun.id else fun s ->
                begin match Subst.find_type x s with
                | None -> let x' = new_var () in Subst.bind_type x (`LVar (x', level)) s
                | Some t -> lift_t bvs t s
                end

        | `Int -> Fun.id
        | `String -> Fun.id
        | `Array t -> lift_t bvs t
        | `Sexp xs -> lift_sexp bvs xs
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in fun s ->
                let s = List.fold_left (Fun.flip @@ lift_c bvs) s c in
                let s = List.fold_left (Fun.flip @@ lift_t bvs) s ts in
                let s = lift_t bvs t s in
                s

        | `Mu (x, t) -> lift_t (IS.add x bvs) t

        and lift_sexp bvs ((xs, _) : sexp) : Mut.t =
            SexpConstructors.fold (fun _ ts s -> List.fold_left (Fun.flip @@ lift_t bvs) s ts) xs

        and lift_p bvs : p -> Mut.t = function
        | `Wildcard -> Fun.id
        | `Typed (t, p) -> fun s -> lift_p bvs p @@ lift_t bvs t s
        | `Array ps -> fun s -> List.fold_left (Fun.flip @@ lift_p bvs) s ps
        | `Sexp (_, ps) -> fun s -> List.fold_left (Fun.flip @@ lift_p bvs) s ps
        | `Boxed -> Fun.id
        | `Unboxed -> Fun.id
        | `StringTag -> Fun.id
        | `ArrayTag -> Fun.id
        | `SexpTag -> Fun.id
        | `FunTag -> Fun.id

        and lift_c bvs : c -> Mut.t = function
        | `Eq (t1, t2) -> fun s -> lift_t bvs t2 @@ lift_t bvs t1 s
        | `Ind (t1, t2) -> fun s -> lift_t bvs t2 @@ lift_t bvs t1 s
        | `Call (t, ts, t') -> fun s ->
            let s = lift_t bvs t s in
            let s = List.fold_left (Fun.flip @@ lift_t bvs) s ts in
            let s = lift_t bvs t' s in
            s

        | `Match (t, ps) -> fun s -> List.fold_left (Fun.flip @@ lift_p bvs) (lift_t bvs t s) ps
        | `Sexp (_, t, ts) -> fun s -> List.fold_left (Fun.flip @@ lift_t bvs) (lift_t bvs t s) ts
        in

        object

            method t = lift_t
            method sexp = lift_sexp
            method p = lift_p
            method c = lift_c
        end

    (* unification, returns substitution and residual equations *)

    exception Unification_failure of Subst.t * t * t
    exception Sexp_unification_failure of Subst.t

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
        | `LVar (_, l) as t1, t2 ->
            (*  example: lv_1^0 = [lv_2^1]
             *  result:  lv_1^0 = [lv_3^0] and lv_2^1 |-> lv_3^0
             *
             *  we need to <<refresh>> lowlevel variables in type `t` with highlevel ones
             *  and record refreshing in result substitution (lv_2^1 |-> lv_3^0),
             *  as a residual we record refreshed equation (lv_1^0 = [lv_3^0])
             *
             *  !!! same operation we need to do with all residual constraints below !!!
             *)

            fun (s, r) ->
                let s = (lift_lvars var_gen l)#t IS.empty t2 s in
                s, (t1, t2) :: r

        | t1, (`LVar (_, _) as t2) -> unify_t (t2, t1)

        (* === term vs term === *)

        | `GVar x, `GVar y when x = y -> Fun.id
        | `Int, `Int -> Fun.id
        | `String, `String -> Fun.id
        | `Array t1, `Array t2 -> unify_t (t1, t2)
        | `Sexp xs1, `Sexp xs2 ->
            begin try unify_sexp (xs1, xs2)
            with Sexp_unification_failure s ->
                raise @@ Unification_failure (s, `Sexp xs1, `Sexp xs2)
            end

        | `Arrow (xs1, c1, ts1, t1), `Arrow (xs2, c2, ts2, t2) -> failwith "TODO: unify arrows"
        | `Mu (x1, t1), `Mu (x2, t2) -> failwith "TODO: unify recursive types"
        | t1, t2 -> fun (s, _) -> raise @@ Unification_failure (s, t1, t2)

        and unify_sexp ((xs1, row1), (xs2, row2)) : Mut.t =
            let rec bind_rows s = function
            | None, None -> s
            | Some row1, None -> Subst.bind_sexp row1 (SexpConstructors.empty, None) s
            | None, Some row2 -> bind_rows s (Some row2, None)
            | Some row1, Some row2 -> Subst.bind_vars row1 row2 s
            in

            let bind_row_sexp s = function
            | None, (xs, None) when SexpConstructors.is_empty xs -> s
            | None, (xs, Some row2) when SexpConstructors.is_empty xs ->
                bind_rows s (None, Some row2)

            | Some row1, xs -> Subst.bind_sexp row1 xs s
            | _ -> raise @@ Sexp_unification_failure s
            in

            let xs1'empty = SexpConstructors.is_empty xs1 in
            let xs2'empty = SexpConstructors.is_empty xs2 in

            if xs1'empty && xs2'empty then begin fun (s, r) ->
                try bind_rows s (row1, row2), r
                with Subst.Need_unification (t1, t2) ->
                    unify_sexp (Subst.unpack_sexp t1, Subst.unpack_sexp t2) (s, r)

            end else if xs1'empty then begin fun (s, r) ->
                try bind_row_sexp s (row1, (xs2, row2)), r
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

                    let f row' xs =
                        unify_sexp ((SexpConstructors.empty, row'), (xs, Some row))
                    in

                    let row1_f = f row1 xs2_only in
                    let row2_f = f row2 xs1_only in

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
            r: c_aux list;
        }

        type fail =
        | Nested of fail list
        | Unification of t * t
        | NotIndexable of t
        | NotCallable of t
        | NotSexp of t
        | WrongArgsNum of t * int

        exception Failure of fail * c_aux * Subst.t
    end

    let simplify var_gen level =
        let open Simpl in

        let unify = unify var_gen level in

        (* shaps = SHallow APply Substitution *)
        let shaps s = function
        | `LVar (x, _) as t ->
            begin match Subst.find_type x s with
            | Some t -> t
            | None -> t
            end

        | t -> t
        in

        let new_var () =
            let idx = !var_gen + 1 in
            var_gen := idx ;

            idx
        in

        let single_step_lvar st l (c, inf : c_aux) =
            if l < level then
                let s = (lift_lvars var_gen l)#c IS.empty c st.s in
                Some ([], { s ; r = (c, inf) :: st.r })

            else None
        in

        let single_step_det st (c, inf as c_aux : c_aux) : (c list * st) option =
            match c with
            | `Eq (t1, t2) -> begin try
                let s, r = unify#t (t1, t2) (st.s, []) in

                let r = List.map (fun (t1, t2) -> `Eq (t1, t2), inf ) r in
                Some ([], { s = s; r = r @ st.r })

                with Unification_failure (s, t1, t2) ->
                    raise @@ Failure (Unification (t1, t2), c_aux, s)
                end

            | `Ind (t1, t2) ->
                begin match shaps st.s t1 with
                | `LVar (_, l) -> single_step_lvar st l c_aux
                | `String -> Some ([`Eq (t2, `Int)], st)
                | `Array t1 -> Some ([`Eq (t1, t2)], st)
                | `Sexp _ -> failwith "TODO: Ind(Sexp)"
                | _ -> raise @@ Failure (NotIndexable t1, c_aux, st.s)
                end

            | `Call (ft, ts, t) ->
                begin match shaps st.s ft with
                | `LVar (_, l) ->
                    (* dirty hack to support polymorphism in recursive functions
                     *
                     * here we utilize the fact that odd levels are special levels for parameters
                     * and force Call-s to stay under forall binder to prevent lifting of argument
                     * types
                     *
                     * it make we able to infer polymorphic functions that uses recursion, because
                     * if argument types lifted too much, they will be monomorphized any way...
                     *)

                    let level = if level mod 2 = 0 then Int.max 0 @@ level - 1 else level in
                    single_step_lvar st (Int.max l level) c_aux

                | `Arrow (_, _, fts, _) ->
                    begin
                        let args_num = List.length ts in
                        if args_num <> List.length fts then
                            raise @@ Failure (WrongArgsNum (ft, args_num), c_aux, st.s)
                    end ;

                    (* TODO: think about recursive Call-s... *)
                    let [@warning "-8"] `Arrow (xs, fc, fts, ft) : t =
                        (apply_subst st.s)#t IS.empty ft
                    in

                    let xs = IM.of_seq @@ Seq.map (fun x -> x, new_var ()) @@ IS.to_seq xs in
                    let gtol = gvars_to_lvars level xs in

                    (* try-with to catch Failure from `gtol` *)

                    try
                        (* Printf.printf "ARROW TYPE: %s\n" @@ show_t @@ `Arrow (xs, fc, fts, ft) ; *)

                        let fc = List.map (gtol#c IS.empty) fc in
                        let fts = List.map (gtol#t IS.empty) fts in
                        let ft = gtol#t IS.empty ft in

                        let c = List.map2 (fun ft t -> `Eq (ft, t)) fts ts in
                        let c = `Eq (ft, t) :: c in
                        let c = fc @ c in

                        Some (c, st)

                    with Stdlib.Failure _ -> None

                | _ -> raise @@ Failure (NotCallable ft, c_aux, st.s)
                end

            | `Sexp (x, t, ts) ->
                begin match shaps st.s t with
                | `LVar (_, l) ->
                    (* we act like Sexp(LVar) is non-deterministic constraint to preserve Sexp
                     * constraints under binder of arrow type and to prevent eager
                     * monomorphization of all S-expression types
                     *)

                    single_step_lvar st l c_aux

                | `Sexp _ ->
                    let xs = SexpConstructors.singleton (x, List.length ts) ts in
                    let t' = `Sexp (xs, Some (new_var ())) in
                    Some ([`Eq (t, t')], st)

                | _ -> raise @@ Failure (NotSexp t, c_aux, st.s)
                end

            | c -> failwith @@ "TODO " ^ show_c c
        in

        let single_step_nondet st (c, inf : c_aux) : (c list * st) list = match c with
        | _ -> Option.to_list @@ single_step_det st (c, inf)
        in

        let one_step_f cs' cs (c, inf : c_aux) (new_cs, st) =
            let f c' = c', { inf with parents = c :: inf.parents } in
            List.rev cs' @ List.map f new_cs @ cs, st
        in

        let one_step_nondet st =
            let rec hlp cs' : c_aux list -> (c_aux list * st) list * c_aux = function
            | [] ->
                (*
                let cs = List.rev cs' in
                let apply_subst = (apply_subst st.s)#c IS.empty in
                let cs = List.map (fun (c, _) -> apply_subst c) cs in
                Printf.printf "CONSTRAINTS: %s\n" @@ show_list show_c cs ;
                *)

                failwith "BUG: no solutions"

            | c :: cs ->
                match single_step_nondet st c with
                | [] -> hlp (c :: cs') cs
                | xs -> List.map (one_step_f cs' cs c) xs, c
            in

            hlp []
        in

        let one_step_nondet cs st = one_step_nondet st cs in

        let one_step_det st =
            let rec hlp cs' : c_aux list -> (c_aux list * st) option = function
            | [] -> None
            | c :: cs ->
                match single_step_det st c with
                | Some res -> Some (one_step_f cs' cs c res)
                | None -> hlp (c :: cs') cs
            in

            hlp []
        in

        let one_step_det cs st = one_step_det st cs in

        (* TODO: actually one_step_nondet and one_step_det differs only in used functor... *)

        let rec full_deterministic cs st : c_aux list * st =
            match one_step_det cs st with
            | None -> cs, st
            | Some (cs, st) -> full_deterministic cs st
        in

        let rec full cs st : st =
            let cs, st = full_deterministic cs st in
            if cs = [] then st else let cs, c = one_step_nondet cs st in full' (st.s, c) [] cs

        and full' (s, c as inf) errs = function
        | [] -> raise @@ Failure (Nested errs, c, s)
        | (cs, st) :: xs ->
            try full cs st
            with Failure (err, _, _) -> full' inf (err :: errs) xs
        in

        object

            method full_deterministic = full_deterministic
            method full = full

            method run : 'a. ?s : Subst.t -> (st -> 'a) -> 'a =
                fun ?(s=Subst.empty) f -> f { s = s; r = [] }
        end

    (* type inferrer *)

    type decl_type = string * t * decl_type list

    let infer () =
        let module E = Expr in

        let prev_var_idx = Stdlib.ref 0 in
        let current_level = Stdlib.ref 0 in

        let public_names = Stdlib.ref Context.empty in
        let current_decls = Stdlib.ref [] in

        let current_path = Stdlib.ref [] in

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
            let f (ps, ctx) p = let p, ctx = infer_p ctx p in p::ps, ctx in
            let ps, ctx = List.fold_left f ([], ctx) ps in
            List.rev ps, ctx
        in

        let rec infer_t ctx (e, inf : Expr.expr) : c_aux list * t =
            let return c = c, { path = !current_path ; pos = inf.pos ; parents = [] } in

            match e with
            | E.Scope (ds, e) ->
                let name_in_path =
                    let prev_path = !current_path in
                    prev_path = [] || inf.name <> List.hd prev_path
                in

                if name_in_path then current_path := inf.name :: !current_path ;

                let c1, ctx = infer_decls ctx ds in
                let c2, t = infer_t ctx e in

                current_decls := List.rev !current_decls ;

                if name_in_path then current_path := List.tl !current_path ;

                c1 @ c2, t

            | E.Seq (l, r) ->
                let c1, _ = infer_t ctx l in
                let c2, t = infer_t ctx r in
                c1 @ c2, t

            | E.Assign (l, r) ->
                let c1, t = infer_t ctx l in
                let c2, t' = infer_t ctx r in
                return (`Eq (t, t')) :: c1 @ c2, t

            | E.Binop (l, r) ->
                let c1, t1 = infer_t ctx l in
                let c2, t2 = infer_t ctx r in
                return (`Eq (t1, `Int)) :: return (`Eq (t2, `Int)) :: c1 @ c2, `Int

            | E.Call (f, xs) ->
                let c, t = infer_t ctx f in
                let cts = List.map (infer_t ctx) xs in
                let c = List.concat_map fst cts @ c in

                let s = new_tv () in
                return (`Call (t, List.map snd cts, s)) :: c, s

            | E.Subscript (x, i) ->
                let c1, t1 = infer_t ctx x in
                let c2, t2 = infer_t ctx i in

                let s = new_tv () in
                return (`Eq (t2, `Int)) :: return (`Ind (t1, s)) :: c1 @ c2, s

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
                let fc = List.map (fun (c, inf) -> apply_subst#c IS.empty c, inf) fc in
                let bc = List.map (fun (c, inf) -> apply_subst#c IS.empty c, inf) bc in
                let t = apply_subst#t IS.empty t in

                let bvs =
                    let level = !current_level in
                    let lvars = lvars @@ fun l -> l >= level in

                    let lvars_c fvs (c, _) = lvars#c IS.empty fvs c in

                    if not @@ IS.is_empty @@ List.fold_left lvars_c IS.empty fc then
                        failwith "BUG: lowlevel variables in free constraints occurred" ;

                    let fvs = IS.empty in
                    let fvs = List.fold_left (lvars#t IS.empty) fvs ts in
                    let fvs = List.fold_left lvars_c fvs bc in
                    let fvs = lvars#t IS.empty fvs t in
                    fvs
                in

                (* to build result type, we need to convert bound variables to ground *)

                let bc, ts, t =
                    let level = !current_level in
                    let lvars_to_gvars = lvars_to_gvars @@ fun l -> l >= level in

                    let ts = List.map (lvars_to_gvars#t IS.empty) ts in
                    let bc = List.map (fun (c, _) -> lvars_to_gvars#c IS.empty c) bc in
                    let t = lvars_to_gvars#t IS.empty t in
                    bc, ts, t
                in

                (* since we discard substitution, apply it on debug info *)
                begin
                    let rec f (x, t, inner) = x, apply_subst#t IS.empty t, List.map f inner in
                    current_decls := List.map f !current_decls
                end ;

                current_level := !current_level - 1 ;

                fc, `Arrow (bvs, bc, ts, t)

            | E.Skip -> [], new_tv ()
            | E.Array xs ->
                let cts = List.map (infer_t ctx) xs in

                let t = new_tv () in
                let c = List.concat_map (fun (c', s) -> return (`Eq (t, s)) :: c') cts in

                c, `Array t

            | E.Sexp (x, xs) ->
                let cts = List.map (infer_t ctx) xs in
                let c = List.concat_map fst cts in

                let t = new_tv () in
                return (`Sexp (x, t, List.map snd cts)) :: c, t

            | E.If (c, t, f) ->
                let c1, _ = infer_t ctx c in
                let c2, t = infer_t ctx t in
                let c3, t' = infer_t ctx f in
                return (`Eq (t, t')) :: c1 @ c2 @ c3, t

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

                let f (cs, ps) (p, b) =
                    let p, ctx = infer_p ctx p in
                    let c', s' = infer_t ctx b in
                    (return (`Eq (s, s')) :: c') :: cs, p::ps
                in

                let cs, ps = List.fold_left f ([c], []) bs in
                let c = List.concat @@ List.rev cs in
                return (`Match (t, ps)) :: c, s

        and infer_decl ctx : E.decl -> _ = function
        | E.Var v, inf ->
            let t' = Context.find inf.name ctx in

            if inf.public then public_names := Context.add inf.name t' !public_names ;

            let old_decls = !current_decls in
            current_decls := [] ;

            let c, t = infer_t ctx v in

            current_decls := (inf.name, t', !current_decls) :: old_decls ;

            (`Eq (t', t), { path = !current_path ; pos = (snd v).pos; parents = [] }) :: c

        | E.Fun (xs, b), inf -> infer_decl ctx (E.Var (E.Lambda (xs, b), snd b), inf)

        and infer_decls ctx ds =
            let f ctx (_, inf : E.decl) = Context.add inf.name (new_tv ()) ctx in
            let ctx = List.fold_left f ctx ds in

            List.concat_map (fun d -> infer_decl ctx d) ds, ctx
        in

        object

            method pattern = infer_p
            method term = infer_t

            method decl = infer_decl
            method decls = infer_decls

            method simplify = simplify prev_var_idx

            method public_names () = !public_names
            method all_decls () = !current_decls
        end

    (* monomorphization of all logic variables *)

    let monomorphize placeholder =
        let rec mono_t bvs : t -> t = function
        | `GVar x as t ->
            if not @@ IS.mem x bvs then failwith "monomorphize: free ground variable" ;
            t

        | `LVar (x, _) ->
            if IS.mem x bvs then failwith "monomorphize: bound logic variable" ;
            placeholder

        | `Int -> `Int
        | `String -> `String
        | `Array t -> `Array (mono_t bvs t)
        | `Sexp xs -> `Sexp (mono_sexp bvs xs)
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            `Arrow (xs, List.map (mono_c bvs) c, List.map (mono_t bvs) ts, mono_t bvs t)

        | `Mu (x, t) -> `Mu (x, mono_t (IS.add x bvs) t)

        and mono_sexp bvs ((xs, _) : sexp) : sexp =
            SexpConstructors.map (List.map @@ mono_t bvs) xs, None

        and mono_p bvs : p -> p = function
        | `Wildcard -> `Wildcard
        | `Typed (t, p) -> `Typed (mono_t bvs t, mono_p bvs p)
        | `Array ps -> `Array (List.map (mono_p bvs) ps)
        | `Sexp (x, ps) -> `Sexp (x, List.map (mono_p bvs) ps)
        | `Boxed -> `Boxed
        | `Unboxed -> `Unboxed
        | `StringTag -> `StringTag
        | `ArrayTag -> `ArrayTag
        | `SexpTag -> `SexpTag
        | `FunTag -> `FunTag

        and mono_c bvs : c -> c = function
        | `Eq (t1, t2) -> `Eq (mono_t bvs t1, mono_t bvs t2)
        | `Ind (t1, t2) -> `Ind (mono_t bvs t1, mono_t bvs t2)
        | `Call (t, ts, t') -> `Call (mono_t bvs t, List.map (mono_t bvs) ts, mono_t bvs t')
        | `Match (t, ps) -> `Match (mono_t bvs t, List.map (mono_p bvs) ps)
        | `Sexp (x, t, ts) -> `Sexp (x, mono_t bvs t, List.map (mono_t bvs) ts)
        in

        object

            method t = mono_t
            method sexp = mono_sexp
            method p = mono_p
            method c = mono_c
        end
end
