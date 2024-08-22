
module type Term = sig

    type t

    val show : t -> string
end

module Make(T : Term) : sig

    type v = int * int

    type t

    exception Need_unification of t * T.t * T.t

    val empty: t

    val find_term: int -> t -> T.t option
    val find_var: v -> t -> v

    val bind_vars: v -> v -> t -> t
    val bind_term: v -> T.t -> t -> t

    val debug_print: t -> unit

end = struct

    module IntMap = Map.Make(Int)

    type v = int * int

    (* DSU node *)
    type node = {

        parent: int;
        level: int;

        term: T.t option;
    }

    type t = {

        (* mutable for path compress, do not break logical immutability! *)
        mutable nodes: node IntMap.t;
    }

    exception Need_unification of t * T.t * T.t

    let empty = { nodes = IntMap.empty }

    let rec find_internal v s = match IntMap.find_opt v s.nodes with
    | None -> v, None
    | Some node ->
        if node.parent = v
        then v, Some node
        else begin
            let parent, parent_node = find_internal node.parent s in

            s.nodes <- IntMap.add v { node with parent = parent } s.nodes ;
            parent, parent_node
        end

    let find_term v s =
        let _, node = find_internal v s in
        Option.bind node @@ fun { term; _ } -> term

    let find_var (v, l) s =
        let v, node = find_internal v s in
        let l = match node with None -> l | Some node -> node.level in
        v, l

    let default_node v l = { parent = v; level = l; term = None }

    let bind_vars (v, l) (u, k) s =
        let v, v_node = find_internal v s in
        let u, u_node = find_internal u s in

        let v_node = Option.value ~default:(default_node v l) v_node in
        let u_node = Option.value ~default:(default_node u k) u_node in

        let term = match v_node.term, u_node.term with
        | Some v_term, _           -> Some v_term
        | _,           Some u_term -> Some u_term
        | None,        None        -> None
        in

        let s = if v_node.level > u_node.level then
            let nodes = IntMap.add v { v_node with parent = u } s.nodes in
            let nodes = IntMap.add u { u_node with term = term } nodes in
            { nodes }

        else
            let nodes = IntMap.add u { u_node with parent = v } s.nodes in
            let nodes = IntMap.add v { v_node with term = term } nodes in
            { nodes }
        in

        match v_node.term, u_node.term with
        | Some v_term, Some u_term -> raise @@ Need_unification (s, v_term, u_term)
        | _ -> s

    let bind_term (v, l) t s =
        let v, v_node = find_internal v s in
        let v_node = Option.value ~default:(default_node v l) v_node in

        begin match v_node.term with
        | Some t' -> raise @@ Need_unification (s, t, t')
        | None -> ()
        end ;

        { nodes = IntMap.add v { v_node with term = Some t } s.nodes }

    let debug_print s =
        let module VS = Set.Make(struct

            type t = int * int

            let compare (x, l) (y, k) =
                if l <> k
                then Int.compare l k
                else Int.compare x y
        end) in

        let vars = Hashtbl.create @@ IntMap.cardinal s.nodes in

        let f x node =
            let x', _ = find_internal x s in
            let xs = Option.value ~default:VS.empty @@ Hashtbl.find_opt vars x' in
            Hashtbl.replace vars x' @@ VS.add (x, node.level) xs
        in

        IntMap.iter f s.nodes ;

        let f x xs =
            let node = IntMap.find x s.nodes in

            let f (x, l) = Printf.sprintf "(%d, %d)" x l in
            let xs = List.of_seq @@ Seq.map f @@ VS.to_seq xs in
            let xs = String.concat ", " xs in

            let l = node.level in
            let t = match node.term with
            | Some t -> T.show t
            | None -> ""
            in

            Printf.printf "{%s} subsumed by (%d, %d) |-> %s\n" xs x l t
        in

        Hashtbl.iter f vars
end
