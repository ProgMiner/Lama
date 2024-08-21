
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
        | `Variable  None    -> Var (Int 0, { name ; pos = { row = 0 ; col = 0 } }), inf
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
    | `Vararg   of t list * t       (* vararg function type *)
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

    (* TODO: add constraint Tuple(T, T, ..., T) *)

    and c = [
    | `Eq       of t * t            (* syntax equality *)
    | `Ind      of t * t            (* indexable *)
    | `IndI     of int * t * t      (* Ind with constant index *)
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

    | `Vararg (ts, t) -> Printf.sprintf "(%s, ...) -> %s" (show_list show_t ts) (show_t t)
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
    | `IndI (i, l, r) -> Printf.sprintf "Ind_%d(%s, %s)" i (show_t l) (show_t r)
    | `Call (t, ts, s) -> Printf.sprintf "Call(%s, %s)" (show_list show_t @@ t :: ts) (show_t s)
    | `Match (t, ps) -> Printf.sprintf "Match(%s, %s)" (show_t t) (show_list show_p ps)
    | `Sexp (x, t, ts) -> Printf.sprintf "Sexp_%s(%s)" x (show_list show_t @@ t :: ts)

    let rec lex_compare = function
    | [] -> 0
    | f :: fs ->
        let x = f () in
        if x = 0 then lex_compare fs else x

    let rec compare_t (t1 : t) (t2 : t) = match t1, t2 with
    | `GVar x, `GVar y -> Int.compare x y
    | `GVar _, _ -> -1
    | _, `GVar _ -> 1
    | `LVar (x, _), `LVar (y, _) -> Int.compare x y
    | `LVar _, _ -> -1
    | _, `LVar _ -> 1
    | `Int, `Int -> 0
    | `Int, _ -> -1
    | _, `Int -> 1
    | `String, `String -> 0
    | `String, _ -> -1
    | _, `String -> 1
    | `Array t1, `Array t2 -> compare_t t1 t2
    | `Array _, _ -> -1
    | _, `Array _ -> 1
    | `Sexp xs, `Sexp ys -> compare_sexp xs ys
    | `Sexp _, _ -> -1
    | _, `Sexp _ -> 1
    | `Arrow (xs1, c1, ts1, t1), `Arrow (xs2, c2, ts2, t2) ->
        lex_compare [ (fun () -> IS.compare xs1 xs2)
                    ; (fun () -> List.compare compare_c c1 c2)
                    ; (fun () -> List.compare compare_t ts1 ts2)
                    ; (fun () -> compare_t t1 t2)
                    ]

    | `Arrow _, _ -> -1
    | _, `Arrow _ -> 1
    | `Vararg (ts1, t1), `Vararg (ts2, t2) ->
        lex_compare [ (fun () -> List.compare compare_t ts1 ts2)
                    ; (fun () -> compare_t t1 t2)
                    ]

    | `Vararg _, _ -> -1
    | _, `Vararg _ -> 1
    | `Mu (x1, t1), `Mu (x2, t2) ->
        lex_compare [ (fun () -> Int.compare x1 x2)
                    ; (fun () -> compare_t t1 t2)
                    ]

    | `Mu _, _ -> -1
    | _, `Mu _ -> 1
    [@@warning "-11"]

    and compare_sexp (xs1, row1 : sexp) (xs2, row2 : sexp) =
        lex_compare [ (fun () -> Option.compare Int.compare row1 row2)
                    ; (fun () -> SexpConstructors.compare (List.compare compare_t) xs1 xs2)
                    ]

    and compare_p (p1 : p) (p2 : p) = match p1, p2 with
    | `Wildcard, `Wildcard -> 0
    | `Wildcard, _ -> -1
    | _, `Wildcard -> 1
    | `Typed (t1, p1), `Typed (t2, p2) ->
        lex_compare [ (fun () -> compare_t t1 t2)
                    ; (fun () -> compare_p p1 p2)
                    ]

    | `Typed _, _ -> -1
    | _, `Typed _ -> 1
    | `Array ps1, `Array ps2 -> List.compare compare_p ps1 ps2
    | `Array _, _ -> -1
    | _, `Array _ -> 1
    | `Sexp (x1, ps1), `Sexp (x2, ps2) ->
        lex_compare [ (fun () -> String.compare x1 x2)
                    ; (fun () -> List.compare compare_p ps1 ps2)
                    ]

    | `Sexp _, _ -> -1
    | _, `Sexp _ -> 1
    | `Boxed, `Boxed -> 0
    | `Boxed, _ -> -1
    | _, `Boxed -> 1
    | `Unboxed, `Unboxed -> 0
    | `Unboxed, _ -> -1
    | _, `Unboxed -> 1
    | `StringTag, `StringTag -> 0
    | `StringTag, _ -> -1
    | _, `StringTag -> 1
    | `ArrayTag, `ArrayTag -> 0
    | `ArrayTag, _ -> -1
    | _, `ArrayTag -> 1
    | `SexpTag, `SexpTag -> 0
    | `SexpTag, _ -> -1
    | _, `SexpTag -> 1
    | `FunTag, `FunTag -> 0
    | `FunTag, _ -> -1
    | _, `FunTag -> 1
    [@@warning "-11"]

    and compare_c (c1 : c) (c2 : c) = match c1, c2 with
    | `Eq (l1, r1), `Eq (l2, r2) ->
        lex_compare [ (fun () -> compare_t l1 l2)
                    ; (fun () -> compare_t r1 r2)
                    ]

    | `Eq _, _ -> -1
    | _, `Eq _ -> 1
    | `Ind (l1, r1), `Ind (l2, r2) ->
        lex_compare [ (fun () -> compare_t l1 l2)
                    ; (fun () -> compare_t r1 r2)
                    ]

    | `Ind _, _ -> -1
    | _, `Ind _ -> 1
    | `IndI (i1, l1, r1), `IndI (i2, l2, r2) ->
        lex_compare [ (fun () -> Int.compare i1 i2)
                    ; (fun () -> compare_t l1 l2)
                    ; (fun () -> compare_t r1 r2)
                    ]

    | `IndI _, _ -> -1
    | _, `IndI _ -> 1
    | `Call (t1, ts1, s1), `Call (t2, ts2, s2) ->
        lex_compare [ (fun () -> compare_t t1 t2)
                    ; (fun () -> List.compare compare_t ts1 ts2)
                    ; (fun () -> compare_t s1 s2)
                    ]

    | `Call _, _ -> -1
    | _, `Call _ -> 1
    | `Match (t1, ps1), `Match (t2, ps2) ->
        lex_compare [ (fun () -> compare_t t1 t2)
                    ; (fun () -> List.compare compare_p ps1 ps2)
                    ]

    | `Match _, _ -> -1
    | _, `Match _ -> 1
    | `Sexp (x1, t1, ts1), `Sexp (x2, t2, ts2) ->
        lex_compare [ (fun () -> String.compare x1 x2)
                    ; (fun () -> compare_t t1 t2)
                    ; (fun () -> List.compare compare_t ts1 ts2)
                    ]

    | `Sexp _, _ -> -1
    | _, `Sexp _ -> 1
    [@@warning "-11"]

    (* substitution *)

    module Subst = struct

        type value
        = Type of t
        | Sexp of sexp

        include Subst.Make(struct

            type t = value

            let show = function
            | Type t -> show_t t
            | Sexp xs -> show_sexp xs
        end)

        let unpack_type = function
        | Type t -> t
        | _ -> failwith "unpack_type: not a type variable"

        let unpack_sexp = function
        | Sexp t -> t
        | _ -> failwith "unpack_sexp: not a row variable"

        let row_level = -1

        let find_row_var row s = fst @@ find_var (row, row_level) s

        let find_type x s = Option.map unpack_type @@ find_term x s
        let find_sexp x s = Option.map unpack_sexp @@ find_term x s

        let bind_row_vars row1 row2 s = bind_vars (row1, row_level) (row2, row_level) s

        let bind_type v t = bind_term v @@ Type t
        let bind_sexp v t = bind_term (v, row_level) @@ Sexp t
    end

    let apply_subst s =
        let vars_path = Stdlib.ref IM.empty in

        let rec subst_t : t -> t = function
        | `GVar _ as t -> t

        | `LVar (x, l) ->
            let x, l = Subst.find_var (x, l) s in

            let old_vars_path = !vars_path in

            if IM.mem x old_vars_path then begin
                (* variable `x` is recursive *)
                vars_path := IM.add x true old_vars_path ;
                `GVar x

            end else begin
                match Subst.find_type x s with
                | None -> `LVar (x, l)
                | Some t ->
                    vars_path := IM.add x false old_vars_path ;

                    let res = subst_t t in

                    let new_vars_path = !vars_path in
                    vars_path := IM.remove x new_vars_path ;

                    (* check is `x` become recursive *)
                    if IM.find x new_vars_path
                    then `Mu (x, res)
                    else res
            end

        | `Int -> `Int
        | `String -> `String
        | `Array t -> `Array (subst_t t)
        | `Sexp xs -> `Sexp (subst_sexp xs)
        | `Arrow (xs, c, ts, t) -> `Arrow (xs, List.map subst_c c, List.map subst_t ts, subst_t t)
        | `Vararg (ts, t) -> `Vararg (List.map subst_t ts, subst_t t)
        | `Mu (x, t) -> `Mu (x, subst_t t)

        and subst_sexp (xs, row) =
            let row = Fun.flip Option.map row @@ Fun.flip Subst.find_row_var s in

            match Option.bind row @@ Fun.flip Subst.find_sexp s with
            | None ->
                let xs = SexpConstructors.map (List.map subst_t) xs in
                xs, row

            | Some (xs', row') ->
                let f _ _ _ = failwith "apply_subst: intersecting constructors in S-exp" in
                let xs = SexpConstructors.union f xs xs' in

                (* tail recursion intended *)
                subst_sexp (xs, row')

        and subst_p : p -> p = function
        | `Wildcard -> `Wildcard
        | `Typed (t, p) -> `Typed (subst_t t, subst_p p)
        | `Array ps -> `Array (List.map subst_p ps)
        | `Sexp (x, ps) -> `Sexp (x, List.map subst_p ps)
        | `Boxed -> `Boxed
        | `Unboxed -> `Unboxed
        | `StringTag -> `StringTag
        | `ArrayTag -> `ArrayTag
        | `SexpTag -> `SexpTag
        | `FunTag -> `FunTag

        and subst_c : c -> c = function
        | `Eq (t1, t2) -> `Eq (subst_t t1, subst_t t2)
        | `Ind (t1, t2) -> `Ind (subst_t t1, subst_t t2)
        | `IndI (i, t1, t2) -> `IndI (i, subst_t t1, subst_t t2)
        | `Call (t, ts, t') -> `Call (subst_t t, List.map subst_t ts, subst_t t')
        | `Match (t, ps) -> `Match (subst_t t, List.map subst_p ps)
        | `Sexp (x, t, ts) -> `Sexp (x, subst_t t, List.map subst_t ts)
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

        let visited = Stdlib.ref IS.empty in

        let module Mut = struct

            type t = Subst.t -> Subst.t
        end in

        let rec lift_t bvs : t -> Mut.t = function
        | `GVar x ->
            if not @@ IS.mem x bvs then failwith "lift_lvars: free ground variable" ;
            Fun.id

        | `LVar (x, l) ->
            if IS.mem x bvs then failwith "lift_lvars: bound logic variable" ;

            fun s ->
                let x, l = Subst.find_var (x, l) s in

                let old_visited = !visited in

                if IS.mem x old_visited then s else begin
                    visited := IS.add x old_visited ;

                    if l <= level then s else
                        begin match Subst.find_type x s with
                        | Some t -> lift_t bvs t s
                        | None ->
                            let x' = new_var () in
                            Subst.bind_vars (x, l) (x', level) s
                        end
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

        | `Vararg (ts, t) -> fun s -> lift_t bvs t @@ List.fold_left (Fun.flip @@ lift_t bvs) s ts
        | `Mu (x, t) -> lift_t (IS.add x bvs) t

        and lift_sexp bvs (xs, row : sexp) : Mut.t = fun s ->
            let f _ ts s = List.fold_left (Fun.flip @@ lift_t bvs) s ts in
            let s = SexpConstructors.fold f xs s in

            let row = Fun.flip Option.map row @@ Fun.flip Subst.find_row_var s in

            match Option.bind row @@ Fun.flip Subst.find_sexp s with
            | Some xs -> lift_sexp bvs xs s
            | None -> s

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
        | `IndI (_, t1, t2) -> fun s -> lift_t bvs t2 @@ lift_t bvs t1 s
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

    (* convert logic variables to ground w.r.t. substitution *)

    let lvars_to_gvars var_gen level p =
        let new_var () =
            let idx = !var_gen + 1 in
            var_gen := idx ;

            idx
        in

        let cache = Stdlib.ref IM.empty in
        let vars = Stdlib.ref IS.empty in

        let map_m f s xs =
            let f (xs, s) x = let x, s = f s x in (x :: xs, s) in
            let xs, s = List.fold_left f ([], s) xs in
            List.rev xs, s
        in

        let map_m_sexp f s xs =
            let f k x (xs, s) = let x, s = f s x in (SexpConstructors.add k x xs, s) in
            SexpConstructors.fold f xs (SexpConstructors.empty, s)
        in

        let rec ltog_t bvs s : t -> t * Subst.t = function
        | `GVar x as t ->
            if not @@ IS.mem x bvs then failwith "lvars_to_gvars: free ground variable" ;
            t, s

        | `LVar (x, l) ->
            if IS.mem x bvs then failwith "lvars_to_gvars: bound logic variable" ;

            let x, l = Subst.find_var (x, l) s in

            begin match Subst.find_type x s with
            | None ->
                if p l then begin
                    vars := IS.add x !vars ;
                    `GVar x, s
                end else begin
                    `LVar (x, l), s
                end

            | Some t ->
                match IM.find_opt x !cache with
                | Some x' -> `LVar (x', level), s
                | None ->
                    let x' = new_var () in
                    cache := IM.add x x' !cache ;

                    let t', s = ltog_t bvs s t in
                    let s = Subst.bind_type (x', level) t' s in
                    `LVar (x', level), s
            end

        | `Int -> `Int, s
        | `String -> `String, s
        | `Array t -> let t, s = ltog_t bvs s t in `Array t, s
        | `Sexp xs -> let xs, s = ltog_sexp bvs s xs in `Sexp xs, s
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            let c, s = map_m (ltog_c bvs) s c in
            let ts, s = map_m (ltog_t bvs) s ts in
            let t, s = ltog_t bvs s t in
            `Arrow (xs, c, ts, t), s

        | `Vararg (ts, t) ->
            let ts, s = map_m (ltog_t bvs) s ts in
            let t, s = ltog_t bvs s t in
            `Vararg (ts, t), s

        | `Mu (x, t) -> let t, s = ltog_t (IS.add x bvs) s t in `Mu (x, t), s

        and ltog_sexp bvs s (xs, row : sexp) : sexp * Subst.t =
            let xs, s = map_m_sexp (map_m @@ ltog_t bvs) s xs in

            let row = Fun.flip Option.map row @@ Fun.flip Subst.find_row_var s in

            match Option.bind row @@ Fun.flip Subst.find_sexp s with
            | None -> (xs, row), s
            | Some xs' ->
                let row = Option.get row in
                match IM.find_opt row !cache with
                | Some row' -> (xs, Some row'), s
                | None ->
                    let row' = new_var () in
                    cache := IM.add row row' !cache ;

                    let xs', s = ltog_sexp bvs s xs' in
                    let s = Subst.bind_sexp row' xs' s in
                    (xs, Some row'), s

        and ltog_p bvs s : p -> p * Subst.t = function
        | `Wildcard -> `Wildcard, s
        | `Typed (t, p) ->
            let t, s = ltog_t bvs s t in
            let p, s = ltog_p bvs s p in
            `Typed (t, p), s

        | `Array ps -> let ps, s = map_m (ltog_p bvs) s ps in `Array ps, s
        | `Sexp (x, ps) -> let ps, s = map_m (ltog_p bvs) s ps in `Sexp (x, ps), s
        | `Boxed -> `Boxed, s
        | `Unboxed -> `Unboxed, s
        | `StringTag -> `StringTag, s
        | `ArrayTag -> `ArrayTag, s
        | `SexpTag -> `SexpTag, s
        | `FunTag -> `FunTag, s

        and ltog_c bvs s : c -> c * Subst.t = function
        | `Eq (t1, t2) ->
            let t1, s = ltog_t bvs s t1 in
            let t2, s = ltog_t bvs s t2 in
            `Eq (t1, t2), s

        | `Ind (t1, t2) ->
            let t1, s = ltog_t bvs s t1 in
            let t2, s = ltog_t bvs s t2 in
            `Ind (t1, t2), s

        | `IndI (i, t1, t2) ->
            let t1, s = ltog_t bvs s t1 in
            let t2, s = ltog_t bvs s t2 in
            `IndI (i, t1, t2), s

        | `Call (t, ts, t') ->
            let t, s = ltog_t bvs s t in
            let ts, s = map_m (ltog_t bvs) s ts in
            let t', s = ltog_t bvs s t' in
            `Call (t, ts, t'), s

        | `Match (t, ps) ->
            let t, s = ltog_t bvs s t in
            let ps, s = map_m (ltog_p bvs) s ps in
            `Match (t, ps), s

        | `Sexp (x, t, ts) ->
            let t, s = ltog_t bvs s t in
            let ts, s = map_m (ltog_t bvs) s ts in
            `Sexp (x, t, ts), s
        in

        object

            method t = ltog_t
            method sexp = ltog_sexp
            method p = ltog_p
            method c = ltog_c

            method vars () = !vars
        end

    (* refresh ground variables with logic w.r.t. substitution *)

    let gvars_to_lvars var_gen level s xs =
        let new_var () =
            let idx = !var_gen + 1 in
            var_gen := idx ;

            idx
        in

        let cache = Hashtbl.create 0 in

        (* counter for number of refreshed variables *)
        let counter = Stdlib.ref 0 in

        let open struct

            type node_info = {

                mutable old_level: int option;

                mutable deps: IS.t;
                mutable changed: bool;

                mutable new_var: int option;
                mutable new_level: int option;
                mutable new_term: Subst.value option;
            }
        end in

        (* inverted dependency graph *)
        let inv_deps = Hashtbl.create 0 in
        let cur_deps = Stdlib.ref IS.empty in

        let get_deps_node x = match Hashtbl.find_opt inv_deps x with
        | Some node -> node
        | None ->
            let node = {
                old_level = None ;
                deps = IS.empty ;
                changed = false ;
                new_var = None ;
                new_level = None ;
                new_term = None ;
            } in

            Hashtbl.add inv_deps x node ;
            node
        in

        let record_dep x y =
            let node = get_deps_node y in
            node.deps <- IS.add x node.deps
        in

        let rec gtol_t bvs : t -> t = function
        | `GVar x as t ->
            if IS.mem x bvs then t else begin
                match IM.find_opt x xs with
                | Some x -> counter := !counter + 1 ; `LVar (x, level)
                | None -> failwith "gvars_to_lvars: free ground variable"
            end

        | `LVar (x, l) ->
            if IS.mem x bvs then failwith "gvars_to_lvars: bound logic variable" ;

            let x, l = Subst.find_var (x, l) s in

            begin match Subst.find_type x s with
            | None ->
                (* assume that there aren't any logic variables that could contain ground variables *)
                `LVar (x, l)

            | Some t ->
                (* current term depends on variable `x` *)
                cur_deps := IS.add x !cur_deps ;

                match Option.bind (Hashtbl.find_opt cache bvs) @@ IM.find_opt x with
                | Some x' -> `LVar (x', level)
                | None ->
                    let x' = new_var () in
                    Hashtbl.replace cache bvs @@ IM.add x x'
                        @@ Option.value ~default:IM.empty
                        @@ Hashtbl.find_opt cache bvs ;

                    let old_deps = !cur_deps in
                    cur_deps := IS.empty ;

                    let old_counter = !counter in
                    let t' = gtol_t bvs t in

                    begin
                        let node = get_deps_node x in

                        node.old_level <- Some l ;
                        node.changed <- !counter <> old_counter ;

                        node.new_var <- Some x' ;
                        node.new_level <- Some level ;
                        node.new_term <- Some (Subst.Type t') ;
                    end ;

                    IS.iter (record_dep x) !cur_deps ;
                    cur_deps := old_deps ;

                    `LVar (x', level)
            end

        | `Int -> `Int
        | `String -> `String
        | `Array t -> `Array (gtol_t bvs t)
        | `Sexp xs -> `Sexp (gtol_sexp bvs xs)
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            `Arrow (xs, List.map (gtol_c bvs) c, List.map (gtol_t bvs) ts, gtol_t bvs t)

        | `Vararg (ts, t) -> `Vararg (List.map (gtol_t bvs) ts, gtol_t bvs t)
        | `Mu (x, t) -> `Mu (x, gtol_t (IS.add x bvs) t)

        and gtol_sexp bvs (xs, row : sexp) : sexp =
            let xs = SexpConstructors.map (List.map @@ gtol_t bvs) xs in

            let row = Fun.flip Option.map row @@ Fun.flip Subst.find_row_var s in

            match Option.bind row @@ Fun.flip Subst.find_sexp s with
            | None -> xs, row
            | Some xs' ->
                let row = Option.get row in

                (* current term depends on variable `row` *)
                cur_deps := IS.add row !cur_deps ;

                match Option.bind (Hashtbl.find_opt cache bvs) @@ IM.find_opt row with
                | Some row' -> xs, Some row'
                | None ->
                    let row' = new_var () in
                    Hashtbl.replace cache bvs @@ IM.add row row'
                        @@ Option.value ~default:IM.empty
                        @@ Hashtbl.find_opt cache bvs ;

                    let old_deps = !cur_deps in
                    cur_deps := IS.empty ;

                    let old_counter = !counter in
                    let xs' = gtol_sexp bvs xs' in

                    begin
                        let node = get_deps_node row in

                        node.old_level <- Some Subst.row_level ;
                        node.changed <- !counter <> old_counter ;

                        node.new_var <- Some row' ;
                        node.new_level <- Some Subst.row_level ;
                        node.new_term <- Some (Subst.Sexp xs') ;
                    end ;

                    IS.iter (record_dep row) !cur_deps ;
                    cur_deps := old_deps ;

                    xs, Some row'

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
        | `IndI (i, t1, t2) -> `IndI (i, gtol_t bvs t1, gtol_t bvs t2)
        | `Call (t, ts, t') -> `Call (gtol_t bvs t, List.map (gtol_t bvs) ts, gtol_t bvs t')
        | `Match (t, ps) -> `Match (gtol_t bvs t, List.map (gtol_p bvs) ps)
        | `Sexp (x, t, ts) -> `Sexp (x, gtol_t bvs t, List.map (gtol_t bvs) ts)
        in

        let finalize () =
            let rec propagate node =
                if node.changed then begin
                    let f y =
                        let node = Hashtbl.find inv_deps y in

                        if not node.changed then begin
                            node.changed <- true ;
                            propagate node
                        end
                    in

                    IS.iter f node.deps
                end
            in

            (* propagate `changed` flag *)
            Hashtbl.iter (fun _ -> propagate) inv_deps ;

            let add_bindings x node =
                let new_var = Option.get node.new_var, Option.get node.new_level in

                if node.changed
                then Subst.bind_term new_var (Option.get node.new_term)
                else Subst.bind_vars new_var (x, Option.get node.old_level)
            in

            Hashtbl.fold add_bindings inv_deps s
        in

        object

            method t bvs t = cur_deps := IS.empty ; gtol_t bvs t
            method sexp bvs xs = cur_deps := IS.empty ; gtol_sexp bvs xs
            method p bvs p = cur_deps := IS.empty ; gtol_p bvs p
            method c bvs c = cur_deps := IS.empty ; gtol_c bvs c

            method finalize = finalize
        end

    (* check has term recursion in substitution *)

    let has_recursion s =
        let path = Stdlib.ref IS.empty in

        let rec is_rec_t bvs : t -> bool = function
        | `GVar x ->
            if not @@ IS.mem x bvs then failwith "has_recursion: free ground variable" ;
            false

        | `LVar (x, l) ->
            if IS.mem x bvs then failwith "has_recursion: bound logic variable" ;

            let x, _ = Subst.find_var (x, l) s in

            let old_path = !path in

            if IS.mem x old_path then true else begin match Subst.find_type x s with
            | None -> false
            | Some t ->
                path := IS.add x old_path ;

                let res = is_rec_t bvs t in

                path := old_path ;

                res
            end

        | `Int -> false
        | `String -> false
        | `Array t -> is_rec_t bvs t
        | `Sexp xs -> is_rec_sexp bvs xs
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            List.exists (is_rec_c bvs) c || List.exists (is_rec_t bvs) ts || is_rec_t bvs t

        | `Vararg (ts, t) -> List.exists (is_rec_t bvs) ts || is_rec_t bvs t
        | `Mu (x, t) -> is_rec_t (IS.add x bvs) t

        and is_rec_sexp bvs ((xs, row) : sexp) : bool =
            if SexpConstructors.exists (fun _ -> List.exists @@ is_rec_t bvs) xs then true else
                let row = Fun.flip Option.map row @@ Fun.flip Subst.find_row_var s in

                begin match Option.bind row @@ Fun.flip Subst.find_sexp s with
                | Some xs -> is_rec_sexp bvs xs
                | None -> false
                end

        and is_rec_p bvs : p -> bool = function
        | `Wildcard -> false
        | `Typed (t, p) -> is_rec_t bvs t || is_rec_p bvs p
        | `Array ps -> List.exists (is_rec_p bvs) ps
        | `Sexp (_, ps) -> List.exists (is_rec_p bvs) ps
        | `Boxed -> false
        | `Unboxed -> false
        | `StringTag -> false
        | `ArrayTag -> false
        | `SexpTag -> false
        | `FunTag -> false

        and is_rec_c bvs : c -> bool = function
        | `Eq (t1, t2) -> is_rec_t bvs t1 || is_rec_t bvs t2
        | `Ind (t1, t2) -> is_rec_t bvs t1 || is_rec_t bvs t2
        | `IndI (_, t1, t2) -> is_rec_t bvs t1 || is_rec_t bvs t2
        | `Call (t, ts, t') -> is_rec_t bvs t || List.exists (is_rec_t bvs) ts || is_rec_t bvs t'
        | `Match (t, ps) -> is_rec_t bvs t || List.exists (is_rec_p bvs) ps
        | `Sexp (_, t, ts) -> is_rec_t bvs t || List.exists (is_rec_t bvs) ts
        in

        object

            method t = is_rec_t
            method sexp = is_rec_sexp
            method p = is_rec_p
            method c = is_rec_c
        end

    let refresh_mu level =
        let cache = Stdlib.ref IS.empty in

        let map_m f s xs =
            let f (xs, s) x = let x, s = f s x in (x :: xs, s) in
            let xs, s = List.fold_left f ([], s) xs in
            List.rev xs, s
        in

        let map_m_sexp f s xs =
            let f k x (xs, s) = let x, s = f s x in (SexpConstructors.add k x xs, s) in
            SexpConstructors.fold f xs (SexpConstructors.empty, s)
        in

        let rec remu_t bvs s : t -> t * Subst.t = function
        | `GVar x ->
            if not @@ IS.mem x bvs then failwith "refresh_mu: free ground variable" ;

            if IS.mem x !cache
            then `LVar (x, level), s
            else `GVar x, s

        | `LVar (x, _) as t ->
            if IS.mem x bvs then failwith "lift_lvars: bound logic variable" ;
            t, s

        | `Int -> `Int, s
        | `String -> `String, s
        | `Array t -> let t, s = remu_t bvs s t in `Array t, s
        | `Sexp xs -> let xs, s = remu_sexp bvs s xs in `Sexp xs, s
        | `Arrow (xs, c, ts, t) ->
            let bvs = IS.union bvs xs in
            let c, s = map_m (remu_c bvs) s c in
            let ts, s = map_m (remu_t bvs) s ts in
            let t, s = remu_t bvs s t in
            `Arrow (xs, c, ts, t), s

        | `Vararg (ts, t) ->
            let ts, s = map_m (remu_t bvs) s ts in
            let t, s = remu_t bvs s t in
            `Vararg (ts, t), s

        | `Mu (x, t) ->
            if IS.mem x !cache then `LVar (x, level), s else begin
                cache := IS.add x !cache ;

                let t, s = remu_t (IS.add x bvs) s t in
                let s = Subst.bind_type (x, level) t s in

                `LVar (x, level), s
            end

        and remu_sexp bvs s (xs, row : sexp) : sexp * Subst.t =
            if row <> None then failwith "BUG: row variables aren't supported" ;

            let xs, s = map_m_sexp (map_m @@ remu_t bvs) s xs in
            (xs, row), s

        and remu_p bvs s : p -> p * Subst.t = function
        | `Wildcard -> `Wildcard, s
        | `Typed (t, p) ->
            let t, s = remu_t bvs s t in
            let p, s = remu_p bvs s p in
            `Typed (t, p), s

        | `Array ps -> let ps, s = map_m (remu_p bvs) s ps in `Array ps, s
        | `Sexp (x, ps) -> let ps, s = map_m (remu_p bvs) s ps in `Sexp (x, ps), s
        | `Boxed -> `Boxed, s
        | `Unboxed -> `Unboxed, s
        | `StringTag -> `StringTag, s
        | `ArrayTag -> `ArrayTag, s
        | `SexpTag -> `SexpTag, s
        | `FunTag -> `FunTag, s

        and remu_c bvs s : c -> c * Subst.t = function
        | `Eq (t1, t2) ->
            let t1, s = remu_t bvs s t1 in
            let t2, s = remu_t bvs s t2 in
            `Eq (t1, t2), s

        | `Ind (t1, t2) ->
            let t1, s = remu_t bvs s t1 in
            let t2, s = remu_t bvs s t2 in
            `Ind (t1, t2), s

        | `IndI (i, t1, t2) ->
            let t1, s = remu_t bvs s t1 in
            let t2, s = remu_t bvs s t2 in
            `IndI (i, t1, t2), s

        | `Call (t, ts, t') ->
            let t, s = remu_t bvs s t in
            let ts, s = map_m (remu_t bvs) s ts in
            let t', s = remu_t bvs s t' in
            `Call (t, ts, t'), s

        | `Match (t, ps) ->
            let t, s = remu_t bvs s t in
            let ps, s = map_m (remu_p bvs) s ps in
            `Match (t, ps), s

        | `Sexp (x, t, ts) ->
            let t, s = remu_t bvs s t in
            let ts, s = map_m (remu_t bvs) s ts in
            `Sexp (x, t, ts), s
        in

        object

            method t = remu_t
            method sexp = remu_sexp
            method p = remu_p
            method c = remu_c
        end

    (* unification, returns substitution and residual equations *)

    exception Unification_failure of Subst.t * t * t
    exception Custom_unification_failure of Subst.t

    let unify var_gen =
        let new_var () =
            let idx = !var_gen + 1 in
            var_gen := idx ;

            idx
        in

        let module VMap = struct

            include Map.Make(Int)

            type nonrec t = int option Stdlib.ref t
        end in

        let module Mut = struct

            type t = Subst.t -> Subst.t
        end in

        let rec unify_t (ctx : VMap.t) : t * t -> Mut.t = function

        (* === var vs var === *)

        | `LVar (x, l), `LVar (y, k) when x = y ->
            if l <> k then failwith "unify: same variable on different levels" ;
            Fun.id

        | `LVar (x, l), `LVar (y, k) ->
            fun s -> begin
                (* `bind_vars` respects leveling *)
                try Subst.bind_vars (x, l) (y, k) s
                with Subst.Need_unification (t1, t2) ->
                    unify_t ctx (Subst.unpack_type t1, Subst.unpack_type t2) s
            end

        (* === var vs term === *)

        | `LVar (x, l), t ->
            fun s -> begin
                (*  example: lv_1^0 = [lv_2^1]
                 *  result:  lv_1^0 = [lv_3^0] and lv_2^1 |-> lv_3^0
                 *
                 *  we need to <<refresh>> lowlevel variables in type `t` with highlevel ones
                 *  and record refreshing in result substitution (lv_2^1 |-> lv_3^0),
                 *  after that we solve the refreshed equation (lv_1^0 = [lv_3^0])
                 *
                 *  !!! same operation we need to do with all residual constraints below !!!
                 *)

                let s = (lift_lvars var_gen l)#t IS.empty t s in

                try Subst.bind_type (x, l) t s
                with Subst.Need_unification (t1, t2) ->
                    unify_t ctx (Subst.unpack_type t1, Subst.unpack_type t2) s
            end

        | t1, (`LVar _ as t2) -> unify_t ctx (t2, t1)

        (* === term vs term === *)

        | `GVar x, `GVar y when x = y -> Fun.id
        | `GVar x, `GVar y when VMap.mem x ctx && VMap.mem y ctx ->
            let x' = VMap.find x ctx in
            let y' = VMap.find y ctx in

            if Option.is_none !x' && Option.is_none !y' then begin
                x' := Some y ;
                y' := Some x ;
                Fun.id
            end else if !x' = Some y && !y' = Some x then
                Fun.id
            else
                fun s -> raise @@ Unification_failure (s, `GVar x, `GVar y)

        | `Int, `Int -> Fun.id
        | `String, `String -> Fun.id
        | `Array t1, `Array t2 -> unify_t ctx (t1, t2)
        | `Sexp xs1, `Sexp xs2 ->
            let unify_sexp = unify_sexp ctx (xs1, xs2) in

            fun s ->
                begin try unify_sexp s
                with Custom_unification_failure s ->
                    raise @@ Unification_failure (s, `Sexp xs1, `Sexp xs2)
                end

        | `Arrow (xs1, c1, ts1, t1) as ft1, (`Arrow (xs2, c2, ts2, t2) as ft2) ->
            if IS.cardinal xs1 <> IS.cardinal xs2 || List.length c1 <> List.length c2
                || List.length ts1 <> List.length ts2 || (xs1 <> xs2 && not (IS.disjoint xs1 xs2))
            then
                fun s -> raise @@ Unification_failure (s, ft1, ft2)

            else
                let ctx = if xs1 = xs2 then ctx else
                    let f x = VMap.add x @@ Stdlib.ref None in
                    let ctx = IS.fold f xs1 ctx in
                    let ctx = IS.fold f xs2 ctx in
                    ctx
                in

                fun s ->
                    let s =
                        try List.fold_left2 (fun s c1 c2 -> unify_c ctx (c1, c2) s) s c1 c2
                        with Custom_unification_failure s ->
                            raise @@ Unification_failure (s, ft1, ft2)
                    in

                    let s = List.fold_left2 (fun s t1 t2 -> unify_t ctx (t1, t2) s) s ts1 ts2 in
                    let s = unify_t ctx (t1, t2) s in
                    s

        | `Vararg (ts1, t1), `Vararg (ts2, t2) -> fun s ->
            let s = unify_t ctx (t1, t2) s in

            let ts'l = Int.min (List.length ts1) (List.length ts2) in
            let ts1 = List.of_seq @@ Seq.take ts'l @@ List.to_seq ts1 in
            let ts2 = List.of_seq @@ Seq.take ts'l @@ List.to_seq ts2 in

            List.fold_left2 (fun s t1 t2 -> unify_t ctx (t1, t2) s) s ts1 ts2

        | `Mu (x1, t1), `Mu (x2, t2) ->
            if x1 = x2 then unify_t ctx (t1, t2) else
                let ctx = VMap.add x1 (Stdlib.ref None) ctx in
                let ctx = VMap.add x2 (Stdlib.ref None) ctx in
                unify_t ctx (t1, t2)

        | t1, t2 -> fun s -> raise @@ Unification_failure (s, t1, t2)

        and unify_sexp (ctx : VMap.t) ((xs1, row1), (xs2, row2)) : Mut.t =
            let rec bind_rows s = function
            | None, None -> s
            | Some row1, None -> Subst.bind_sexp row1 (SexpConstructors.empty, None) s
            | None, Some row2 -> bind_rows s (Some row2, None)
            | Some row1, Some row2 -> Subst.bind_row_vars row1 row2 s
            in

            let bind_row_sexp s = function
            | None, (xs, None) when SexpConstructors.is_empty xs -> s
            | None, (xs, Some row2) when SexpConstructors.is_empty xs ->
                bind_rows s (None, Some row2)

            | Some row1, xs -> Subst.bind_sexp row1 xs s
            | _ -> raise @@ Custom_unification_failure s
            in

            let xs1'empty = SexpConstructors.is_empty xs1 in
            let xs2'empty = SexpConstructors.is_empty xs2 in

            if xs1'empty && xs2'empty then begin fun s ->
                try bind_rows s (row1, row2)
                with Subst.Need_unification (t1, t2) ->
                    unify_sexp ctx (Subst.unpack_sexp t1, Subst.unpack_sexp t2) s

            end else if xs1'empty then begin fun s ->
                try bind_row_sexp s (row1, (xs2, row2))
                with Subst.Need_unification (t1, t2) ->
                    unify_sexp ctx (Subst.unpack_sexp t1, Subst.unpack_sexp t2) s

            end else if xs2'empty then begin
                unify_sexp ctx ((xs2, row2), (xs1, row1))

            end else begin
                let module SLS = Set.Make(SexpLabel) in

                let fst (l, _) = l in
                let xs1'labels = SLS.of_seq @@ Seq.map fst @@ SexpConstructors.to_seq xs1 in
                let xs2'labels = SLS.of_seq @@ Seq.map fst @@ SexpConstructors.to_seq xs2 in

                let both_f' x s =
                    let ts1 = SexpConstructors.find x xs1 in
                    let ts2 = SexpConstructors.find x xs2 in

                    List.fold_left2 (fun s t1 t2 -> unify_t ctx (t1, t2) s) s ts1 ts2
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
                        unify_sexp ctx ((SexpConstructors.empty, row'), (xs, Some row))
                    in

                    let row1_f = f row1 xs2_only in
                    let row2_f = f row2 xs1_only in

                    fun s -> row2_f @@ row1_f @@ both_f s

                end else begin
                    let only_f = unify_sexp ctx ((xs1_only, row1), (xs2_only, row2)) in
                    fun s -> only_f @@ both_f s
                end
            end

        and unify_p (ctx : VMap.t) : p * p -> Mut.t = function
        | `Wildcard, `Wildcard -> Fun.id
        | `Typed (t1, p1), `Typed (t2, p2) -> fun s ->
            let s = unify_t ctx (t1, t2) s in
            let s = unify_p ctx (p1, p2) s in
            s

        | `Array ps1, `Array ps2 when List.length ps1 = List.length ps2 -> fun s ->
            List.fold_left2 (fun s p1 p2 -> unify_p ctx (p1, p2) s) s ps1 ps2

        | `Sexp (x1, ps1), `Sexp (x2, ps2)
        when x1 = x2 && List.length ps1 = List.length ps2 -> fun s ->
            List.fold_left2 (fun s p1 p2 -> unify_p ctx (p1, p2) s) s ps1 ps2

        | `Boxed, `Boxed -> Fun.id
        | `Unboxed, `Unboxed -> Fun.id
        | `StringTag, `StringTag -> Fun.id
        | `ArrayTag, `ArrayTag -> Fun.id
        | `SexpTag, `SexpTag -> Fun.id
        | `FunTag, `FunTag -> Fun.id
        | _, _ -> fun s -> raise @@ Custom_unification_failure s

        and unify_c (ctx : VMap.t) : c * c -> Mut.t = function
        | `Eq (l1, r1), `Eq (l2, r2) -> fun s ->
            let s = unify_t ctx (l1, l2) s in
            let s = unify_t ctx (r1, r2) s in
            s

        | `Ind (l1, r1), `Ind (l2, r2) -> fun s ->
            let s = unify_t ctx (l1, l2) s in
            let s = unify_t ctx (r1, r2) s in
            s

        | `IndI (i1, l1, r1), `IndI (i2, l2, r2) when i1 = i2 -> fun s ->
            let s = unify_t ctx (l1, l2) s in
            let s = unify_t ctx (r1, r2) s in
            s

        | `Call (ft1, ts1, t1), `Call (ft2, ts2, t2)
        when List.length ts1 = List.length ts2 -> fun s ->
            let s = unify_t ctx (ft1, ft2) s in
            let s = List.fold_left2 (fun s t1 t2 -> unify_t ctx (t1, t2) s) s ts1 ts2 in
            let s = unify_t ctx (t1, t2) s in
            s

        | `Match (t1, ps1), `Match (t2, ps2) when List.length ps1 = List.length ps2 -> fun s ->
            let s = unify_t ctx (t1, t2) s in
            let s = List.fold_left2 (fun s p1 p2 -> unify_p ctx (p1, p2) s) s ps1 ps2 in
            s

        | `Sexp (x1, t1, ts1), `Sexp (x2, t2, ts2)
        when x1 = x2 && List.length ts1 = List.length ts2 -> fun s ->
            let s = unify_t ctx (t1, t2) s in
            let s = List.fold_left2 (fun s t1 t2 -> unify_t ctx (t1, t2) s) s ts1 ts2 in
            s

        | _, _ -> fun s -> raise @@ Custom_unification_failure s
        in

        object

            method t = unify_t VMap.empty
            method sexp = unify_sexp VMap.empty
        end

    (* constraints simplifier *)

    module Simpl = struct

        type st = {

            s: Subst.t;
            r: c_aux list;

            unification_handlers: unh list IM.t;
        }

        (* unification handler is a function that is called when logic variable
         * is unified to add new constraints or change state
         * they are used to track new constructors of S-exp types
         * `finalize` must present final state, after that this handler may safely disappear
         *)
        and unh = {

            on_unify: st -> c list * st;
            finalize: st -> st;
        }

        type fail_form =
        | Nested of fail list
        | Unification of t * t
        | NotIndexable of t
        | NotCallable of t
        | NotMatchable of t * p list
        | NotSexp of t
        | WrongArgsNum of t * int
        | IndexOutOfBounds of t * int
        | NotSupported

        and fail = fail_form * c_aux * Subst.t

        exception Failure of fail
    end

    let simplify var_gen params_level level =
        let open Simpl in

        let new_var () =
            let idx = !var_gen + 1 in
            var_gen := idx ;

            idx
        in

        let rec match_t : p * t -> (t list * (t * p) list) option = function
        | `Wildcard, `Int -> Some ([], [])
        | `Wildcard, `String -> Some ([], [])
        | `Wildcard, `Array t -> Some ([], [t, `Wildcard])
        | `Wildcard, `Sexp (xs, None) when SexpConstructors.cardinal xs = 1 ->
            let ts = snd @@ SexpConstructors.find_first (fun _ -> true) xs in
            Some ([], List.map (fun t -> t, `Wildcard) ts)

        | `Wildcard, `Arrow _ -> Some ([], [])
        | `Wildcard, `Vararg _ -> Some ([], [])
        | `Typed (t', p), t -> Option.map (fun (eqs, ps) -> t' :: eqs, ps) @@ match_t (p, t)
        | `Array ps, `Array t -> Some ([], List.map (fun p -> t, p) ps)
        | `Sexp (x, ps), `Sexp (xs, None) when SexpConstructors.cardinal xs = 1 ->
            let ts = SexpConstructors.find_opt (x, List.length ps) xs in
            Option.map (fun ts -> [], List.combine ts ps) ts

        | `Boxed, `String -> Some ([], [])
        | `Boxed, `Array t -> Some ([], [t, `Wildcard])
        | `Boxed, `Sexp (xs, None) when SexpConstructors.cardinal xs = 1 ->
            let ts = snd @@ SexpConstructors.find_first (fun _ -> true) xs in
            Some ([], List.map (fun t -> t, `Wildcard) ts)

        | `Boxed, `Arrow _ -> Some ([], [])
        | `Boxed, `Vararg _ -> Some ([], [])
        | `Unboxed, `Int -> Some ([], [])
        | `StringTag, `String -> Some ([], [])
        | `ArrayTag, `Array t -> Some ([], [t, `Wildcard])
        | `SexpTag, `Sexp (xs, None) when SexpConstructors.cardinal xs = 1 ->
            let ts = snd @@ SexpConstructors.find_first (fun _ -> true) xs in
            Some ([], List.map (fun t -> t, `Wildcard) ts)

        | `FunTag, `Arrow _ -> Some ([], [])
        | `FunTag, `Vararg _ -> Some ([], [])
        | _, `GVar _ -> failwith "match_t: ground variable"
        | _, `LVar _ -> failwith "match_t: logic variable"
        | _, `Sexp (xs, _) when SexpConstructors.cardinal xs <> 1 ->
            failwith "match_t: bruh moment"

        | _, `Mu _ -> failwith "match_t: recursive type"
        | _ -> None
        in

        let group_by_fst xs =
            let res = Hashtbl.create @@ List.length xs in
            Hashtbl.add_seq res @@ List.to_seq xs ;
            res
        in

        let hashtbl_to_assoc xs =
            let xs = Hashtbl.to_seq xs in

            let xs = Seq.group (fun (k1, _) (k2, _) -> k1 = k2) xs in
            let xs = Seq.map List.of_seq xs in

            Seq.map (fun xs -> fst @@ List.hd xs, List.map snd xs) xs
        in

        let combine_hashtbls xs =
            let sz = List.fold_left (fun c xs -> c + Hashtbl.length xs) 0 xs in
            let res = Hashtbl.create sz in

            let f xs = Seq.iter (fun (k, xs) -> Hashtbl.add res k xs) @@ hashtbl_to_assoc xs in
            List.iter f xs ;

            res
        in

        let product_lists =
            let rec hlp acc = function
            | [] -> acc
            | xs :: xs' -> hlp (Seq.map_product (fun x xs -> x :: xs) (List.to_seq xs) acc) xs'
            in

            fun xs -> List.of_seq @@ hlp (List.to_seq [[]]) xs
        in

        let exception Match_failure in

        let match_t_ast st t ps t' : c list * st =
            let ps = List.filter_map (fun p -> match_t (p, t')) ps in

            if ps = [] then raise Match_failure ;

            let eqs = List.concat_map fst ps in
            let eqs = List.map (fun t' -> `Eq (t, t')) eqs in

            let ps = combine_hashtbls @@ List.map (fun (_, ps) -> group_by_fst ps) ps in
            let ps = List.of_seq @@ hashtbl_to_assoc ps in

            (* here we have list of pairs, where first component is type and second is
             * list of lists of patterns, came from different patterns
             *
             * now we need to get cartesian product of lists of patterns
             * to get patterns for one Match
             *
             * in fact, if one pattern returned one type several times,
             * it must be matched with all returned sub-patterns
             *
             * but if one type returned from several patterns,
             * it must be matched with any of sub-patterns...
             *)

            let ps = List.map (fun (t, ps) -> t, product_lists ps) ps in

            (* remove fully Wildcard Match-s to prevent infinite recursion on recursive types *)
            let ps =
                let f ps = List.exists (fun p -> p <> `Wildcard) ps in
                List.map (fun (t, ps) -> t, List.filter f ps) ps
            in

            let ps = List.concat_map (fun (t, ps) -> List.map (fun ps -> `Match (t, ps)) ps) ps in
            eqs @ ps, st
        in

        let unify = unify var_gen in

        (* shaps = SHallow APply Substitution *)
        let rec shaps s = function
        | `LVar (x, l) ->
            let x, l = Subst.find_var (x, l) s in

            begin match Subst.find_type x s with
            | Some t -> shaps s t
            | None -> `LVar (x, l)
            end

        | `Sexp (xs, row) ->
            let rec shaps_sexp acc : int option -> sexp = function
            | None -> acc, None
            | Some row ->
                let row = Subst.find_row_var row s in

                match Subst.find_sexp row s with
                | None -> acc, Some row
                | Some (xs, row) ->
                    let f _ _ _ = failwith "simplify: intersecting constructors in S-exp" in
                    let xs = SexpConstructors.union f acc xs in
                    shaps_sexp xs row
            in

            `Sexp (shaps_sexp xs row)

        | t -> t
        in

        let add_unh x unh st =
            let unhs = st.unification_handlers in

            let unhs' = match IM.find_opt x unhs with Some unhs' -> unhs' | None -> [] in
            let unhs' = unh :: unhs' in

            let unhs = IM.add x unhs' unhs in
            { st with unification_handlers = unhs }
        in

        let finalize_force_empty_row row ({ s ; _ } as st) =
            (* TODO: looks bad *)

            let s =
                try Subst.bind_sexp row (SexpConstructors.empty, None) s
                with Subst.Need_unification (Subst.Sexp x1, Subst.Sexp x2) ->
                    if x1 <> x2 then
                        failwith @@ Printf.sprintf "[%s ; %s]" (show_sexp x1) (show_sexp x2) ;

                    s
            in

            { st with s }
        in

        let single_step_det st (c, inf as c_aux : c_aux) : (c list * st) option =
            let handle_lvar l =
                if l < level then
                    let s = (lift_lvars var_gen l)#c IS.empty c st.s in
                    Some ([], { st with s ; r = (c, inf) :: st.r })

                else None
            in

            (* TODO: infer from context (residuals) *)

            let find_rec_call ft =
                let f = function
                | `Call (ft', _, _) -> shaps st.s ft' = ft
                | _ -> false
                in

                List.find_opt f inf.parents
            in

            match c with
            | `Eq (t1, t2) -> begin try
                let s = unify#t (t1, t2) st.s in

                let old_unh, unh = IM.partition (fun x _ -> Option.is_some @@ Subst.find_term x s)
                    st.unification_handlers
                in

                let st = { st with s ; unification_handlers = unh } in

                let f (cs, st) unh = let cs', st = unh.on_unify st in cs' @ cs, st in
                let f _ unh acc = List.fold_left f acc unh in
                let res = IM.fold f old_unh ([], st) in

                Some res

                with Unification_failure (s, t1, t2) ->
                    raise @@ Failure (Unification (t1, t2), c_aux, s)
                end

            | `Ind (t1, t2) ->
                begin match shaps st.s t1 with
                | `LVar (_, l) -> handle_lvar l
                | `String -> Some ([`Eq (t2, `Int)], st)
                | `Array t1 -> Some ([`Eq (t1, t2)], st)
                | `Sexp (xs, row) ->
                    let xs = SexpConstructors.to_seq xs in
                    let xs = Seq.concat_map (fun (_, ts) -> List.to_seq ts) xs in
                    let xs = List.of_seq @@ Seq.map (fun t -> `Eq (t, t2)) xs in

                    let st = match row with
                    | None -> st
                    | Some row ->
                        let on_unify ({ s ; _ } as st) =
                            let [@warning "-8"] (Some sexp) = Subst.find_sexp row s in
                            [`Ind (`Sexp sexp, t2)], st
                        in

                        let finalize = finalize_force_empty_row row in

                        add_unh row { on_unify ; finalize } st
                    in

                    Some (xs, st)

                | _ -> raise @@ Failure (NotIndexable t1, c_aux, st.s)
                end

            | `IndI (i, t1, t2) ->
                begin match shaps st.s t1 with
                | `LVar (_, l) -> handle_lvar l
                | `Sexp (xs, row) ->
                    let f ts = match List.nth_opt ts i with
                    | None -> raise @@ Failure (IndexOutOfBounds (t1, i), c_aux, st.s)
                    | Some t -> `Eq (t, t2)
                    in

                    let xs = SexpConstructors.to_seq xs in
                    let xs = List.of_seq @@ Seq.map (fun (_, ts) -> f ts) xs in

                    let st = match row with
                    | None -> st
                    | Some row ->
                        let on_unify ({ s ; _ } as st) =
                            let [@warning "-8"] (Some sexp) = Subst.find_sexp row s in
                            [`IndI (i, `Sexp sexp, t2)], st
                        in

                        let finalize = finalize_force_empty_row row in

                        add_unh row { on_unify ; finalize } st
                    in

                    Some (xs, st)

                | _ -> Some ([`Ind (t1, t2)], st)
                end

            | `Call (ft, ts, t) ->
                begin match shaps st.s ft with
                | `LVar (_, l) ->
                    (* here we utilize the fact that there is special level for parameters
                     * and force Call-s to stay under forall binder to prevent lifting
                     * of argument types
                     *
                     * it make we able to infer polymorphic functions that uses recursion, because
                     * if argument types lifted too much, they will be monomorphized any way...
                     *)

                    handle_lvar @@ Int.max l params_level

                | `Arrow (xs, fc, fts, ft) as ft' ->
                    begin
                        let args_num = List.length ts in
                        if args_num <> List.length fts then
                            raise @@ Failure (WrongArgsNum (ft', args_num), c_aux, st.s)
                    end ;

                    let fc, fts, ft, s =
                        match find_rec_call ft' with
                        | None ->
                            (* special case when no bound variables in function type
                             *
                             * in this case we have no need to refresh variables
                             * and able to allow logic variables in type
                             *)

                            if IS.is_empty xs then fc, fts, ft, st.s else begin

                                let f x = x, new_var () in
                                let xs = IM.of_seq @@ Seq.map f @@ IS.to_seq xs in

                                let gtol = gvars_to_lvars var_gen level st.s xs in
                                let fc = List.map (gtol#c IS.empty) fc in
                                let fts = List.map (gtol#t IS.empty) fts in
                                let ft = gtol#t IS.empty ft in
                                let s = gtol#finalize () in

                                fc, fts, ft, s
                            end

                        (* if we found that current Call produced by Call on the same type,
                         * we just require that current call signature is same with previous
                         *
                         * it disables polymorphic recursion but a good way to
                         * allow monomorphic recursive functions
                         *)
                        | Some (`Call (_, ts', t')) -> [], ts', t', st.s
                        | Some _ -> failwith "BUG: find_rec_call returned not Call constraint"
                    in

                    let st = { st with s } in

                    let c = List.map2 (fun ft t -> `Eq (ft, t)) fts ts in
                    let c = `Eq (ft, t) :: c in
                    let c = fc @ c in

                    Some (c, st)

                | `Vararg (fts, ft) as ft' ->
                    begin
                        let args_num = List.length ts in
                        if args_num < List.length fts then
                            raise @@ Failure (WrongArgsNum (ft', args_num), c_aux, st.s)
                    end ;

                    let c =
                        let ts'l = Int.min (List.length fts) (List.length ts) in

                        (* `List.length ts` must be >= `List.length fts` *)
                        let ts = List.of_seq @@ Seq.take ts'l @@ List.to_seq ts in
                        List.map2 (fun ft t -> `Eq (ft, t)) fts ts
                    in

                    let c = `Eq (ft, t) :: c in

                    Some (c, st)

                | _ -> raise @@ Failure (NotCallable ft, c_aux, st.s)
                end

            | `Match (t, ps) ->
                let not_matchable () = raise @@ Failure (NotMatchable (t, ps), c_aux, st.s) in

                begin match shaps st.s t with
                | `LVar (_, l) -> handle_lvar l

                | `Sexp (xs, row) as t ->
                    let f x ts (cs, st) =
                        let t' = `Sexp (SexpConstructors.singleton x ts, None) in
                        let cs', st = match_t_ast st t ps t' in
                        cs' :: cs, st
                    in

                    let st = match row with
                    | None -> st
                    | Some row ->
                        let on_unify st = [`Match (t, ps)], st in
                        let finalize = finalize_force_empty_row row in

                        add_unh row { on_unify ; finalize } st
                    in

                    begin try
                        let cs, st = SexpConstructors.fold f xs ([], st) in
                        Some (List.concat @@ List.rev cs, st)
                    with Match_failure -> not_matchable ()
                    end

                | t -> try Some (match_t_ast st t ps t) with Match_failure -> not_matchable ()
                end

            | `Sexp (x, t, ts) ->
                begin match shaps st.s t with
                | `LVar (_, l) ->
                    (* we act like Sexp(LVar) is non-deterministic constraint to preserve Sexp
                     * constraints under binder of arrow type and to prevent eager
                     * monomorphization of all S-expression types
                     *)

                    handle_lvar l

                | `Sexp _ ->
                    let xs = SexpConstructors.singleton (x, List.length ts) ts in
                    let t' = `Sexp (xs, Some (new_var ())) in
                    Some ([`Eq (t, t')], st)

                | _ -> raise @@ Failure (NotSexp t, c_aux, st.s)
                end

            | _ -> raise @@ Failure (NotSupported, c_aux, st.s)
            [@@warning "-11"]
        in

        let single_step_nondet greedy st (c, inf : c_aux) : (c list * st) list =
            let gen =
                let f (t1, t2) = `Eq (t1, t2) in

                (* we preserve `c` to delegate main work to deterministic steps *)
                let f eqs = List.map f eqs @ [c], st in

                List.map f
            in

            match c with
            | `Ind (t1, t2) | `IndI (_, t1, t2) ->
                begin match shaps st.s t1 with
                | `LVar (_, l) when l >= level ->
                    let row = new_var () in

                    gen [ [t1, `String]
                        ; [t1, `Array t2]
                        ; [t1, `Sexp (SexpConstructors.empty, Some row)]
                        ]

                | _ -> Option.to_list @@ single_step_det st (c, inf)
                end

            | `Call (ft, ts, t) when greedy > 2 ->
                begin match shaps st.s ft with
                | `LVar (_, l) when l >= level -> gen [[ft, `Arrow (IS.empty, [], ts, t)]]
                | _ -> Option.to_list @@ single_step_det st (c, inf)
                end

            | `Match (t, _) ->
                begin match shaps st.s t with
                | `LVar (_, l) when l >= level && greedy > 0 ->
                    gen [ [t, `Int]
                        ; [t, `String]
                        ; [t, `Array (`LVar (new_var (), l))]
                        ; [t, `Sexp (SexpConstructors.empty, Some (new_var ()))]
                        ]

                | _ -> Option.to_list @@ single_step_det st (c, inf)
                end

            | `Sexp (_, t, _) ->
                begin match shaps st.s t with
                | `LVar (_, l) when l >= level ->
                    let row = new_var () in

                    gen [[t, `Sexp (SexpConstructors.empty, Some row)]]

                | _ -> Option.to_list @@ single_step_det st (c, inf)
                end

            | _ -> Option.to_list @@ single_step_det st (c, inf)
        in

        let one_step_f cs' cs (c, inf : c_aux) (new_cs, st) =
            let f c' = c', { inf with parents = c :: inf.parents } in
            List.rev_append cs' @@ List.map f new_cs @ cs, st
        in

        let one_step_nondet st =
            let rec hlp greedy cs' : c_aux list -> (c_aux list * st) list * c_aux = function
            | [] ->
                if greedy < 5
                then hlp (greedy + 1) [] @@ List.rev cs'
                else begin
                    let cs = List.rev cs' in
                    let apply_subst = (apply_subst st.s)#c in
                    let cs = List.map (fun (c, _) -> apply_subst c) cs in
                    Printf.printf "CONSTRAINTS: %s\n" @@ show_list show_c cs ;

                    failwith "BUG: no solutions"
                end

            | c :: cs ->
                match single_step_nondet greedy st c with
                | [] -> hlp greedy (c :: cs') cs
                | xs -> List.map (one_step_f cs' cs c) xs, c
            in

            hlp 0 []
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
        | [] ->
            begin match errs with
            | [err] -> raise @@ Failure err
            | _ -> raise @@ Failure (Nested errs, c, s)
            end

        | (cs, st) :: xs ->
            try full cs st
            with Failure err -> full' inf (err :: errs) xs
        in

        let finalize ({ unification_handlers ; _ } as st) =
            let st = { st with unification_handlers = IM.empty } in

            let f st unh = unh.finalize st in
            let f _ unh st = List.fold_left f st unh in
            let st = IM.fold f unification_handlers st in

            if not @@ IM.is_empty st.unification_handlers then
                failwith "BUG: unification handlers aren't disappear after finalize" ;

            st
        in

        object

            method full_deterministic = full_deterministic
            method full = full

            method run : 'a. ?unification_handlers: Simpl.unh list IM.t -> Subst.t -> (st -> 'a) -> 'a =
                fun ?(unification_handlers=IM.empty) s f -> f { s = s ; r = [] ; unification_handlers }

            method finalize = finalize
        end

    (* type inferrer *)

    type decl_type = string * t * decl_type list

    let infer prev_var =
        let module E = Expr in

        let prev_var_idx = Stdlib.ref prev_var in
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

        | Pattern.Const 0 -> `Wildcard, ctx
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

        let module St = struct

            type 'a t = Subst.t -> 'a * Subst.t

            let return x s = (x, s)
            let bind m k s = let x, s = m s in k x s

            let traverse f ini xs s =
                let f (acc, s) x = let acc, s = f acc x s in acc, s in
                let res, s = List.fold_left f (ini, s) xs in
                res, s

            module Syntax = struct

                let (let*) = bind
            end

            let map_m f xs =
                let open Syntax in
                let f xs x = let* x = f x in return (x :: xs) in
                let* xs = traverse f [] xs in
                return @@ List.rev xs
        end in

        let open St.Syntax in

        let rec infer_t ctx (e, inf : Expr.expr) : (c_aux list * t) St.t =
            let return c = c, { path = !current_path ; pos = inf.pos ; parents = [] } in

            match e with
            | E.Scope (ds, e) ->
                let name_in_path =
                    let prev_path = !current_path in
                    prev_path = [] || inf.name <> List.hd prev_path
                in

                if name_in_path then current_path := inf.name :: !current_path ;

                let* c1, ctx = infer_decls ctx ds in
                let* c2, t = infer_t ctx e in

                current_decls := List.rev !current_decls ;

                if name_in_path then current_path := List.tl !current_path ;

                St.return (c1 @ c2, t)

            | E.Seq (l, r) ->
                let* c1, _ = infer_t ctx l in
                let* c2, t = infer_t ctx r in
                St.return (c1 @ c2, t)

            | E.Assign (l, r) ->
                let* c1, t = infer_t ctx l in
                let* c2, t' = infer_t ctx r in
                St.return (return (`Eq (t, t')) :: c1 @ c2, t)

            | E.Binop (l, r) ->
                let* c1, t1 = infer_t ctx l in
                let* c2, t2 = infer_t ctx r in
                St.return (return (`Eq (t1, `Int)) :: return (`Eq (t2, `Int)) :: c1 @ c2, `Int)

            | E.Call (f, xs) ->
                let* c, t = infer_t ctx f in
                let* cts = St.map_m (infer_t ctx) xs in
                let c = List.concat_map fst cts @ c in

                let t' = new_tv () in
                St.return (return (`Call (t, List.map snd cts, t')) :: c, t')

            | E.Subscript (x, (E.Int i, _)) ->
                let* c, t' = infer_t ctx x in

                let t = new_tv () in
                St.return (return (`IndI (i, t', t)) :: c, t)

            | E.Subscript (x, i) ->
                let* c1, t1 = infer_t ctx x in
                let* c2, t2 = infer_t ctx i in

                let t = new_tv () in
                St.return (return (`Eq (t2, `Int)) :: return (`Ind (t1, t)) :: c1 @ c2, t)

            | E.Name x ->
                begin try St.return ([], Context.find x ctx)
                with Not_found ->
                    failwith @@ Printf.sprintf "infer: unbound variable \"%s\" at [%d:%d, %s]"
                        x inf.pos.row inf.pos.col inf.name
                end

            | E.Int 0 -> St.return ([], new_tv ())
            | E.Int _ -> St.return ([], `Int)
            | E.String _ -> St.return ([], `String)
            | E.Lambda (xs, b) -> fun s ->
                (* here we generate variables for parameters on special level `k` *)

                current_level := !current_level + 1 ;

                let xts = List.map (fun x -> x, new_tv ()) xs in

                (* fictive variable on high level to prevent overmonomorphization *)
                let t = new_tv () in

                (* next we infer_t type of body on lower level (`k + 1`)
                 * and simplify them on this level
                 *)

                current_level := !current_level + 1 ;

                let ctx' = List.fold_left (fun ctx (x, t) -> Context.add x t ctx) ctx xts in
                let (c, t'), s = infer_t ctx' b s in
                let c = return (`Eq (t, t')) :: c in

                let Simpl.{ s ; r = c ; unification_handlers } =
                    let level = !current_level in
                    let simplify = simplify prev_var_idx (level - 1) level in
                    simplify#run s @@ simplify#full c
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

                let bc, s, fc =
                    let level = !current_level in
                    let simplify = simplify prev_var_idx level level in
                    let bc, st = simplify#run ~unification_handlers s @@ simplify#full_deterministic c in
                    let Simpl.{ s ; r ; unification_handlers } = simplify#finalize st in
                    let _ = unification_handlers in
                    bc, s, r
                in

                (* now we have two kinds of residual constraints:
                 * "true" residual constraints are free since we unable to solve them on level `k`,
                 * other returned constraints are bound since we unable to solve them deterministically
                 *
                 * to build result type, we need to convert bound variables to ground
                 *)

                let ts = List.map snd xts in

                let xs, bc, ts, t, s =
                    let level = !current_level in
                    let lvars_to_gvars = lvars_to_gvars prev_var_idx level @@ fun l -> l >= level in

                    let ts, s = St.map_m (Fun.flip @@ lvars_to_gvars#t IS.empty) ts s in
                    let bc, s = St.map_m (fun (c, _) s -> lvars_to_gvars#c IS.empty s c) bc s in
                    let t, s = lvars_to_gvars#t IS.empty s t in
                    let xs = lvars_to_gvars#vars () in
                    xs, bc, ts, t, s
                in

                current_level := !current_level - 1 ;

                let bc = List.sort_uniq compare_c bc in

                (fc, `Arrow (xs, bc, ts, t)), s

            | E.Skip -> St.return ([], new_tv ())
            | E.Array xs ->
                let* cts = St.map_m (infer_t ctx) xs in

                let t = new_tv () in
                let c = List.concat_map (fun (c', s) -> return (`Eq (t, s)) :: c') cts in

                St.return (c, `Array t)

            | E.Sexp (x, xs) ->
                let* cts = St.map_m (infer_t ctx) xs in
                let c = List.concat_map fst cts in

                let t = new_tv () in
                St.return (return (`Sexp (x, t, List.map snd cts)) :: c, t)

            | E.If (c, t, f) ->
                let* c1, _ = infer_t ctx c in
                let* c2, t = infer_t ctx t in
                let* c3, t' = infer_t ctx f in
                St.return (return (`Eq (t, t')) :: c1 @ c2 @ c3, t)

            | E.While (c, b) ->
                let* c1, _ = infer_t ctx c in
                let* c2, _ = infer_t ctx b in
                St.return (c1 @ c2, new_tv ())

            | E.DoWhile (b, c) ->
                let* c1, _ = infer_t ctx b in
                let* c2, _ = infer_t ctx c in
                St.return (c1 @ c2, new_tv ())

            | E.Case (x, bs) ->
                let* c, t = infer_t ctx x in
                let s = new_tv () in

                let f (cs, ps) (p, b) =
                    let p, ctx = infer_p ctx p in
                    let* c', s' = infer_t ctx b in
                    St.return ((return (`Eq (s, s')) :: c') :: cs, p::ps)
                in

                let* cs, ps = St.traverse f ([c], []) bs in
                let c = List.concat @@ List.rev cs in
                St.return (return (`Match (t, ps)) :: c, s)

        and infer_decl ctx : E.decl -> (c_aux list) St.t = function
        | E.Var v, inf ->
            let t' = Context.find inf.name ctx in

            if inf.public then public_names := Context.add inf.name t' !public_names ;

            let old_decls = !current_decls in
            current_decls := [] ;

            let* c, t = infer_t ctx v in

            current_decls := (inf.name, t', !current_decls) :: old_decls ;

            let c' = `Eq (t', t), { path = !current_path ; pos = (snd v).pos ; parents = [] } in
            St.return @@ c' :: c

        | E.Fun (xs, b), inf -> infer_decl ctx (E.Var (E.Lambda (xs, b), snd b), inf)

        and infer_decls ctx ds : (c_aux list * t Context.t) St.t =
            let f ctx (_, inf : E.decl) = Context.add inf.name (new_tv ()) ctx in
            let ctx = List.fold_left f ctx ds in

            let* c = St.map_m (infer_decl ctx) ds in
            St.return (List.concat c, ctx)
        in

        object

            method pattern = infer_p
            method term = infer_t

            method decl = infer_decl
            method decls = infer_decls

            method simplify = simplify prev_var_idx 0

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

        | `Vararg (ts, t) -> `Vararg (List.map (mono_t bvs) ts, mono_t bvs t)
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
        | `IndI (i, t1, t2) -> `IndI (i, mono_t bvs t1, mono_t bvs t2)
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

open Ostap

module Interface = struct

    (* Generates an interface file *)
    let gen ctx =
        let buf = Buffer.create 256 in
        let append str = Buffer.add_string buf str in
        let append_i x = append (string_of_int x) in

        let append_list ?(prefix="") ?(suffix="") ?(sep=", ") append_x = function
        | [] -> ()
        | x :: xs ->
            append prefix ;
            append_x x ;
            List.iter (fun x -> append sep ; append_x x) xs ;
            append suffix
        in

        let rec append_t = function
        | `GVar x -> append_i x
        | `LVar _ -> failwith "BUG: logic variable in typed interface"
        | `Int -> append "Int"
        | `String -> append "String"
        | `Array t -> append "[" ; append_t t ; append "]"
        | `Sexp xs -> append_sexp xs
        | `Arrow (xs, c, ts, t) ->
            append "forall" ;

            append_list ~prefix:" " append_i @@ Type.IS.elements xs ;
            append "." ;

            append_list ~prefix:" " append_c c ;

            append " => (" ;
            append_list append_t ts ;
            append ") -> " ;
            append_t t

        | `Vararg (ts, t) ->
            append "(" ;
            append_list ~suffix:", " append_t ts ;
            append "...) -> " ;
            append_t t

        | `Mu (x, t) ->
            append "mu " ;
            append_i x ;
            append ". " ;
            append_t t

        and append_sexp (xs, row : Type.sexp) =
            if row <> None then failwith "BUG: row variable in typed interface" ;

            let f ((x, _), ts) = append x ; append_list ~prefix:" (" ~suffix:")" append_t ts in
            append_list ~sep:" + " f @@ Type.SexpConstructors.bindings xs

        and append_p = function
        | `Wildcard -> append "_"
        | `Typed (t, p) -> append_t t ; append " @ " ; append_p p
        | `Array ps -> append "[" ; append_list append_p ps ; append "]"
        | `Sexp (x, ps) -> append x ; append_list ~prefix:" (" ~suffix:")" append_p ps
        | `Boxed -> append "#box"
        | `Unboxed -> append "#val"
        | `StringTag -> append "#string"
        | `ArrayTag -> append "#array"
        | `SexpTag -> append "#sexp"
        | `FunTag -> append "#fun"

        and append_c = function
        | `Eq _ -> failwith "BUG: Eq constraint in typed interface"
        | `Ind (t1, t2) -> append "Ind (" ; append_t t1 ; append ", " ; append_t t2 ; append ")"
        | `IndI (i, t1, t2) ->
            append "IndI (" ;
            append_i i ;
            append ", " ;
            append_t t1 ;
            append ", " ;
            append_t t2 ;
            append ")"

        | `Call (ft, ts, t) ->
            append "Call (" ;
            append_t ft ;
            append_list ~prefix:", " append_t ts ;
            append ", " ;
            append_t t ;
            append ")"

        | `Match (t, ps) ->
            append "Match (" ;
            append_t t ;
            append_list ~prefix:", " append_p ps ;
            append ")"

        | `Sexp (x, t, ts) ->
            append "Sexp (" ;
            append x ;
            append ", " ;
            append_t t ;
            append_list ~prefix:", " append_t ts ;
            append ")"
        in

        Type.Context.iter (fun x t -> append x ; append " : " ; append_t t ; append " ;\n") ctx ;
        Buffer.contents buf

    (* Read an interface file *)
    let [@ocaml.warning "-26-27"] read max_var fname =
        let on_var x = max_var := Int.max !max_var x in

        let ostap (
            decl   : i:IDENT ":" t:typ ";" { (i, t) } ;
            typ    : tVar | tInt | tString | tArray | tSexp | tArrow | tVararg | tMu ;
            tVar   : v:DECIMAL { on_var v ; `GVar v } ;
            tInt   : "Int" { `Int } ;
            tString: "String" { `String } ;
            tArray : "[" t:typ "]" { `Array t } ;
            tSexp  : xs:(!(Util.listBy)[ostap (" + ")][tSexpC]) {
                let f xs (x, ts) = Type.SexpConstructors.add (x, List.length ts) ts xs in
                let xs = List.fold_left f Type.SexpConstructors.empty xs in
                `Sexp (xs, None)
            } ;
            tSexpC : x:IDENT ts:(-"(" (!(Util.list)[typ]) -")")? {
                x, match ts with None -> [] | Some ts -> ts
            } ;
            tArrow : "forall" xs:(!(Util.list0)[ostap (DECIMAL)])
                     "." c:(!(Util.list0)[cnstr])
                     "=>" "(" ts:(!(Util.list0)[typ]) ")"
                     "->" t:typ
            {
                List.iter on_var xs ;
                `Arrow (Type.IS.of_seq @@ List.to_seq xs, c, ts, t)
            } ;
            tVararg: "(" ts:(!(Util.list)[typ] -"," | (!(Combinators.empty)) { [] }) -"..." ")"
                     "->" t:typ { `Vararg (ts, t) } ;
            tMu    : "mu" x:DECIMAL "." t:typ { on_var x ; `Mu (x, t) } ;
            pat    : pWildcard | pTyped | pArray | pSexp | pBoxed | pUnboxed
                   | pStringTag | pArrayTag | pSexpTag | pFunTag ;
            pWildcard: "_" { `Wildcard } ;
            pTyped : t:typ "@" p:pat { `Typed (t, p) } ;
            pArray : "[" ps:(!(Util.list0)[pat]) "]" { `Array ps } ;
            pSexp  : x:IDENT ps:(-"(" (!(Util.list)[pat]) -")")? {
                `Sexp (x, match ps with None -> [] | Some ps -> ps)
            } ;
            pBoxed : "#box" { `Boxed } ;
            pUnboxed: "#val" { `Unboxed } ;
            pStringTag: "#string" { `StringTag } ;
            pArrayTag: "#array" { `ArrayTag } ;
            pSexpTag: "#sexp" { `SexpTag } ;
            pFunTag: "#fun" { `FunTag } ;
            cnstr  : cInd | cIndI | cCall | cMatch | cSexp ;
            cInd   : "Ind" "(" t1:typ "," t2:typ ")" { `Ind (t1, t2) } ;
            cIndI  : "IndI" "(" i:DECIMAL "," t1:typ "," t2:typ ")" { `IndI (i, t1, t2) } ;
            cCall  : "Call" "(" ft:typ "," ts:(typ -",")* t:typ ")" { `Call (ft, ts, t) } ;
            cMatch : "Match" "(" t:typ ps:(-"," pat)* ")" { `Match (t, ps) } ;
            cSexp  : "Sexp" "(" x:IDENT "," t:typ ts:(-"," typ)* ")" { `Sexp (x, t, ts) } ;
            interface: decl*
        ) in

        try
            let s = Util.read fname in

            begin match Util.parse (object
                inherit Matcher.t s
                inherit Util.Lexers.ident ["Int"; "String"; "forall"; "mu"] s
                inherit Util.Lexers.decimal s
                inherit Util.Lexers.skip  [Matcher.Skip.whitespaces " \t\n"] s
            end) (ostap (interface -EOF)) with
            | `Ok intfs -> Some intfs
            | `Fail err ->
                failwith @@ Printf.sprintf "malformed typed interface file \"%s\": %s" fname err
            end
        with Sys_error _ -> None

    let find max_var paths import : string * (string * Type.t) list =
        let import' = import ^ ".ti" in

        let rec inner = function
        | [] -> None
        | p::paths ->
            begin match read max_var @@ Filename.concat p import' with
            | Some i -> Some (p, i)
            | None -> inner paths
            end
        in

        match inner paths with
        | Some (path, intfs) -> path, intfs
        | None -> failwith
            @@ Printf.sprintf "could not find a typed interface file for import \"%s\"" import
end
