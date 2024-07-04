
module type Term = sig

    type t
end

module Make(T : Term) : sig

    type t

    exception Need_unification of T.t * T.t

    val empty: t

    val find: int -> t -> T.t option

    val bind_vars: int -> int -> t -> t
    val bind_term: int -> T.t -> t -> t

end = struct

    module IntMap = Map.Make(Int)

    (* DSU node *)
    type node = {

        parent: int;
        depth: int;

        term: T.t option;
    }

    type t = {

        (* mutable for path compress, do not break immutability! *)
        mutable nodes: node IntMap.t;
    }

    exception Need_unification of T.t * T.t

    let empty = { nodes = IntMap.empty }

    let rec find_internal v s = match IntMap.find_opt v s.nodes with
    | None -> v, None
    | Some node ->
        if node.parent = v
        then v, Some node
        else begin
            let parent, parent_node = find_internal node.parent s in

            s.nodes <- IntMap.add v { parent = parent; depth = 0; term = None } s.nodes ;
            parent, parent_node
        end

    let find v s =
        let _, node = find_internal v s in
        Option.bind node @@ fun { term; _ } -> term

    let default_node v = { parent = v; depth = 0; term = None }

    let bind_vars v u s =
        let v, v_node = find_internal v s in
        let u, u_node = find_internal u s in

        let v_node = Option.value ~default:(default_node v) v_node in
        let u_node = Option.value ~default:(default_node u) u_node in

        let term = match v_node.term, u_node.term with
        | Some v_term, Some u_term -> raise @@ Need_unification (v_term, u_term)
        | Some v_term, None        -> Some v_term
        | None,        Some u_term -> Some u_term
        | None,        None        -> None
        in

        if v_node.depth < u_node.depth then
            let nodes = IntMap.add v { parent = u; depth = 0; term = None } s.nodes in
            let nodes = IntMap.add u { u_node with term = term } nodes in
            { nodes = nodes }

        else if u_node.depth < v_node.depth then
            let nodes = IntMap.add u { parent = v; depth = 0; term = None } s.nodes in
            let nodes = IntMap.add v { v_node with term = term } nodes in
            { nodes = nodes }

        else
            let nodes = IntMap.add v { parent = u; depth = 0; term = None } s.nodes in
            let nodes = IntMap.add u { u_node with depth = u_node.depth + 1; term = term } nodes in
            { nodes = nodes }

    let bind_term v t s =
        let v, v_node = find_internal v s in
        let v_node = Option.value ~default:(default_node v) v_node in

        begin match v_node.term with
        | Some t' -> raise @@ Need_unification (t, t')
        | None -> ()
        end ;

        { nodes = IntMap.add v { v_node with term = Some t } s.nodes }
end
