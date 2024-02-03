
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
    | L.Leave -> raise (Invalid_argument "Leave")
    | L.Intrinsic _ -> raise (Invalid_argument "Intrinsic")
    | L.Control _ -> raise (Invalid_argument "Control")

    and decl_from_language = function
    | x, (_, `Fun      (xs,  t)) -> Fun (x, xs, from_language t)
    | x, (_, `Variable  None   ) -> Var (x, Int 0)
    | x, (_, `Variable (Some t)) -> Var (x, from_language t)

    (* convert all scrutinees to variables, don't erase Named patterns *)

    let case_of_variable_pass ast =
        let module M = struct
            module SS = Set.Make(String)

            let idx = Stdlib.ref 0

            let rec next_var ctx =
                let cur_idx = !idx + 1 in
                idx := cur_idx ;

                let var = Printf.sprintf "var!%d" cur_idx in

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
