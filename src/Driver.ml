exception Commandline_error of string

class options args =
  let n = Array.length args in
  let dump_ast = 0b1 in
  let dump_sm = 0b010 in
  let dump_source = 0b100 in
  (* Kakadu: binary masks are cool for C code, but for OCaml I don't see any reason to save memory like this *)
  let help_string =
    "Lama compiler. (C) JetBrains Reserach, 2017-2020.\n"
    ^ "Usage: lamac <options> <input file>\n\n"
    ^ "When no options specified, builds the source file into executable.\n"
    ^ "Options:\n" ^ "  -c        --- compile into object file\n"
    ^ "  -o <file> --- write executable into file <file>\n"
    ^ "  -I <path> --- add <path> into unit search path list\n"
    ^ "  -i        --- interpret on a source-level interpreter\n"
    ^ "  -s        --- compile into stack machine code and interpret on the \
       stack machine initerpreter\n"
    ^ "  -dp       --- dump AST (the output will be written into .ast file)\n"
    ^ "  -dsrc     --- dump pretty-printed source code\n"
    ^ "  -ds       --- dump stack machine code (the output will be written \
       into .sm file; has no\n"
    ^ "                effect if -i option is specfied)\n"
    ^ "  -b        --- compile to a stack machine bytecode\n"
    ^ "  -v        --- show version\n" ^ "  -h        --- show this help\n"
  in
  object (self)
    val version = ref false
    val help = ref false
    val i = ref 1
    val infile = ref (None : string option)
    val outfile = ref (None : string option)
    val paths = ref [ X86.get_std_path () ]
    val mode = ref (`Default : [ `Default | `Eval | `SM | `Compile | `BC | `TC ])
    val curdir = Unix.getcwd ()
    val debug = ref false

    (* Workaround until Ostap starts to memoize properly *)
    val const = ref false

    (* end of the workaround *)
    val dump = ref 0

    initializer
    let rec loop () =
      match self#peek with
      | Some opt ->
          (match opt with
          (* Workaround until Ostap starts to memoize properly *)
          | "-w" -> self#set_workaround
          (* end of the workaround *)
          | "-c" -> self#set_mode `Compile
          | "-o" -> (
              match self#peek with
              | None ->
                  raise
                    (Commandline_error "File name expected after '-o' specifier")
              | Some fname -> self#set_outfile fname)
          | "-I" -> (
              match self#peek with
              | None ->
                  raise (Commandline_error "Path expected after '-I' specifier")
              | Some path -> self#add_include_path path)
          | "-s" -> self#set_mode `SM
          | "-b" -> self#set_mode `BC
          | "-i" -> self#set_mode `Eval
          | "-t" -> self#set_mode `TC
          | "-ds" -> self#set_dump dump_sm
          | "-dsrc" -> self#set_dump dump_source
          | "-dp" -> self#set_dump dump_ast
          | "-h" -> self#set_help
          | "-v" -> self#set_version
          | "-g" -> self#set_debug
          | _ ->
              if opt.[0] = '-' then
                raise
                  (Commandline_error
                     (Printf.sprintf "Invalid command line specifier ('%s')" opt))
              else self#set_infile opt);
          loop ()
      | None -> ()
    in
    loop ()

    (* Workaround until Ostap starts to memoize properly *)
    method is_workaround = !const
    method private set_workaround = const := true

    (* end of the workaround *)
    method private set_help = help := true
    method private set_version = version := true
    method private set_dump mask = dump := !dump lor mask

    method private set_infile name =
      match !infile with
      | None -> infile := Some name
      | Some name' ->
          raise
            (Commandline_error
               (Printf.sprintf "Input file ('%s') already specified" name'))

    method private set_outfile name =
      match !outfile with
      | None -> outfile := Some name
      | Some name' ->
          raise
            (Commandline_error
               (Printf.sprintf "Output file ('%s') already specified" name'))

    method private add_include_path path = paths := path :: !paths

    method private set_mode s =
      match !mode with
      | `Default -> mode := s
      | _ -> raise (Commandline_error "Extra compilation mode specifier")

    method private peek =
      let j = !i in
      if j < n then (
        incr i;
        Some args.(j))
      else None

    method get_mode = !mode

    method get_output_option =
      match !outfile with
      | None -> Printf.sprintf "-o %s" self#basename
      | Some name -> Printf.sprintf "-o %s" name

    method get_absolute_infile =
      let f = self#get_infile in
      if Filename.is_relative f then Filename.concat curdir f else f

    method get_infile =
      match !infile with
      | None -> raise (Commandline_error "Input file not specified")
      | Some name -> name

    method get_help = !help
    method get_include_paths = !paths

    method basename =
      Filename.chop_suffix (Filename.basename self#get_infile) ".lama"

    method topname =
      match !mode with `Compile -> "init" ^ self#basename | _ -> "main"

    method dump_file ext contents =
      let name = self#basename in
      let outf = open_out (Printf.sprintf "%s.%s" name ext) in
      Printf.fprintf outf "%s" contents;
      close_out outf

    method dump_AST ast =
      if !dump land dump_ast > 0 then (
        let buf = Buffer.create 1024 in
        Buffer.add_string buf "<html>";
        Buffer.add_string buf
          (Printf.sprintf "<title> %s </title>" self#get_infile);
        Buffer.add_string buf "<body><li>";
        GT.html Language.Expr.t ast buf;
        Buffer.add_string buf "</li></body>";
        Buffer.add_string buf "</html>";
        self#dump_file "html" (Buffer.contents buf))

    method dump_source (ast : Language.Expr.t) =
      if !dump land dump_source > 0 then Pprinter.pp Format.std_formatter ast

    method dump_SM sm =
      if !dump land dump_sm > 0 then self#dump_file "sm" (SM.show_prg sm)
      else ()

    method greet =
      (match !outfile with
      | None -> ()
      | Some _ -> (
          match !mode with
          | `Default -> ()
          | _ -> Printf.printf "Output file option ignored in this mode.\n"));
      if !version then Printf.printf "%s\n" Version.version;
      if !help then Printf.printf "%s" help_string

    method get_debug = if !debug then "" else "-g"
    method set_debug = debug := true
  end

let[@ocaml.warning "-32"] main =
  try
    let cmd = new options Sys.argv in
    cmd#greet;
    match
      try Language.run_parser cmd
      with Language.Semantic_error msg -> `Fail msg
    with
    | `Ok prog -> (
        cmd#dump_AST (snd prog);
        cmd#dump_source (snd prog);
        match cmd#get_mode with
        | `Default | `Compile -> ignore @@ X86.build cmd prog
        | `BC -> SM.ByteCode.compile cmd (SM.compile cmd prog)
        | `TC ->
            let module T = Typing in

            let prog' = T.Expr.from_language cmd#basename @@ snd prog in

            let max_var = Stdlib.ref 0 in
            let ctx =
                let mods = fst @@ fst prog in
                let ctx = List.map (T.Interface.find max_var cmd#get_include_paths) mods in
                let ctx = List.flatten @@ List.map snd ctx in

                let f ctx (x, t) = T.Type.Context.add x t ctx in
                List.fold_left f T.Type.Context.empty ctx
            in

            Printf.printf "Max variable: %d\n" !max_var ;

            print_endline "Context:" ;
            T.Type.Context.iter (fun x t -> Printf.printf "%s : %s\n" x (T.Type.show_t t)) ctx ;

            (* TODO: unfold recursive types in loaded context *)

            let print_decls decls =
                let rec f indent (x, t, inner) =
                    Printf.printf "%s- %s : %s\n" indent x @@ T.Type.show_t t ;
                    List.iter (f @@ indent ^ "  ") inner
                in

                List.iter (f "") decls
            in

            let print_pub_decls decls =
                let f x t = Printf.printf "- %s : %s\n" x (T.Type.show_t t) in
                T.Type.Context.iter f decls
            in

            let show_c_info_short ({ pos; path; _ } : T.Type.c_info) =
                let path = String.concat "." @@ List.rev path in
                Printf.sprintf "%d:%d, %s" pos.row pos.col path
            in

            begin try
                let infer = T.Type.infer !max_var in
                let (c, _), s = infer#term ctx prog' T.Type.Subst.empty in
                let decls = infer#all_decls () in

                print_endline "Inferred constraints:" ;
                List.iter (fun (c, inf) ->
                    Printf.printf "- %s - %s\n" (show_c_info_short inf) (T.Type.show_c c)) c ;

                print_endline "Inferred types:" ;
                print_decls decls ;

                print_endline "Source substitution:" ;
                T.Type.Subst.debug_print s ;

                let simplify = infer#simplify 0 in
                let st = simplify#run s @@ simplify#full c in
                let T.Type.Simpl.{ s; r = c ; unification_handlers } = simplify#finalize st in
                let _ = unification_handlers in

                (*
                print_endline @@ "Substitution: { " ^ S.Subst.fold (fun v t acc ->
                    let t = T.Type.show_t t in
                    if acc = ""
                    then Printf.sprintf "tv_%d -> %s" v t
                    else Printf.sprintf "%s; tv_%d -> %s" acc v t
                ) subst "" ^ " }";
                *)

                if c <> [] then failwith "BUG: simplify on level 0 returned residuals" ;

                print_endline "Result substitution:" ;
                T.Type.Subst.debug_print s ;

                let finish_types =
                    let monomorphize = (T.Type.monomorphize `Int)#t T.Type.IS.empty in
                    let apply_subst = (T.Type.apply_subst s)#t in
                    fun t -> monomorphize @@ apply_subst t
                in

                let decls =
                    let rec hlp (x, t, inner) = x, finish_types t, List.map hlp inner in
                    List.map hlp decls
                in

                print_endline "Result:" ;
                print_decls decls ;

                let decls = infer#public_names () in
                let decls = T.Type.Context.map finish_types decls in
                print_endline "Public declarations:" ;
                print_pub_decls decls ;

                (* TODO: save typed interface file for modularity *)

            with T.Type.Simpl.Failure err ->
                let open T.Type.Simpl in

                let rec print_err ind (err, (c, inf), s) =
                    let apply_subst = T.Type.apply_subst s in

                    Printf.printf "%s+ at [%s] " ind (show_c_info_short @@ inf) ;

                    begin match err with
                    | Nested errs ->
                        Printf.printf "nested errors:\n" ;
                        List.iter (print_err @@ ind ^ "| ") errs

                    | Unification (t1, t2) ->
                        let apply_subst = apply_subst#t in

                        Printf.printf "unable to unify types:\n" ;
                        Printf.printf "%s| - %s\n" ind @@ T.Type.show_t @@ apply_subst t1 ;
                        Printf.printf "%s| - %s\n" ind @@ T.Type.show_t @@ apply_subst t2 ;

                    | NotIndexable t ->
                        let t = T.Type.show_t @@ apply_subst#t t in
                        Printf.printf "type is not indexable: %s\n" t ;

                    | NotCallable t ->
                        let t = T.Type.show_t @@ apply_subst#t t in
                        Printf.printf "type is not callable: %s\n" t ;

                    | NotMatchable (t, ps) ->
                        let t = T.Type.show_t @@ apply_subst#t t in
                        Printf.printf "type is not matchable with following patterns: %s\n" t ;

                        let f p = T.Type.show_p @@ apply_subst#p p in
                        let ps = List.map f ps in

                        List.iter (Printf.printf "%s| - %s\n" ind) ps

                    | NotSexp t ->
                        let t = T.Type.show_t @@ apply_subst#t t in
                        Printf.printf "type is not S-expression type: %s\n" t ;

                    | WrongArgsNum (t, n) ->
                        let t = T.Type.show_t @@ apply_subst#t t in
                        Printf.printf "wrong number of arguments (given %d) in call: %s\n" n t ;

                    | NotSupported ->
                        let c = T.Type.show_c @@ apply_subst#c c in
                        Printf.printf "constraint solving is not supported: %s\n" c ;
                    end ;

                    let c = c :: inf.parents in
                    let c = List.map apply_subst#c c in

                    Printf.printf "%s+ failed constraint solution trace:\n" ind ;
                    List.iter (fun c -> Printf.printf "%s| - %s\n" ind @@ T.Type.show_c c) c ;
                in

                Printf.printf "Type inference failed:\n" ;
                print_err "" err ;

                exit 1
            end
        | _ ->
            let rec read acc =
              try
                let r = read_int () in
                Printf.printf "> ";
                read (acc @ [ r ])
              with End_of_file -> acc
            in
            let input = read [] in
            let output =
              if cmd#get_mode = `Eval then Language.eval prog input
              else SM.run (SM.compile cmd prog) input
            in
            List.iter (fun i -> Printf.printf "%d\n" i) output)
    | `Fail er ->
        Printf.eprintf "Error: %s\n" er;
        exit 255
  with
  | Language.Semantic_error msg ->
      Printf.printf "Error: %s\n" msg;
      exit 255
  | Commandline_error msg ->
      Printf.printf "%s\n" msg;
      exit 255
