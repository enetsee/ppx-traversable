open Ppxlib
open Ast_builder.Default

let raise_unsupported loc =
  Location.raise_errorf
    ~loc
    "Unsupported use of traversable (you can only use it on a closed types)"
;;

module Inspect = struct
  (* let type_decl td = let loc = td.ptype_loc in match td.ptype_kind with |
     Ptype_variant constr_decls -> let _ = List.map (fun cd -> let args =
     cd.pcd_args in cd ) constr_decls in (??) | Ptype_abstract -> (??) |
     Ptype_record lbl_decls -> let _ =List.map (fun f -> f) lbl_decls in (??) |
     Ptype_open -> raise_unsupported loc *)
end

module Common = struct
  (** If the type is named `t` the module (containing functors to make
      traversable instances for a given applicative) is named `Traversable`
      otherwise the type name is added as a suffix separated by an `_` *)
  let traversable_module = function
    | "t" -> "Traversable"
    | ty_name -> "Traversable_" ^ ty_name
  ;;

  (** Functor paramater for a module exposing an `Applicative` interface as
      defined by `Base`. See
      https://github.com/janestreet/base/blob/master/src/applicative_intf.ml *)
  let ap_param_base ~loc =
    let ty = Located.mk ~loc "t" in
    let ty_long = Located.mk ~loc @@ Lident "t" in
    let ty_con inner = Ast_helper.Typ.(constr ty_long [ inner ]) in
    Named
      ( Located.mk ~loc @@ Some "A"
      , pmty_signature
          ~loc
          [ psig_type
              ~loc
              Recursive
              Ast_helper.[ Type.mk ty ~params:[ Typ.var "a", Invariant ] ]
          ; psig_value
              ~loc
              Ast_helper.(
                Val.mk
                  (Located.mk ~loc "return")
                  Typ.(arrow Nolabel (var "a") @@ ty_con @@ var "a"))
          ; psig_value
              ~loc
              Ast_helper.(
                Val.mk
                  (Located.mk ~loc "map")
                  Typ.(
                    arrow
                      Nolabel
                      (ty_con @@ var "a")
                      (arrow
                         (Labelled "f")
                         (arrow Nolabel (var "a") (var "b"))
                         (ty_con @@ var "b"))))
          ; psig_value
              ~loc
              Ast_helper.(
                Val.mk
                  (Located.mk ~loc "apply")
                  Typ.(
                    arrow
                      Nolabel
                      (ty_con @@ arrow Nolabel (var "a") (var "b"))
                      (arrow Nolabel (ty_con @@ var "a") (ty_con @@ var "b"))))
          ] )
  ;;
end

module Gen_sig = struct
  let ap_traverse_fn ~loc =
    let ty_long_t = Located.mk ~loc @@ Lident "t" in
    let ty_long_A_t = Located.mk ~loc @@ Ldot (Lident "A", "t") in
    let ty_con_t inner = Ast_helper.Typ.(constr ty_long_t [ inner ]) in
    let ty_con_A_t inner = Ast_helper.Typ.(constr ty_long_A_t [ inner ]) in
    let name = Ast_builder.Default.Located.mk ~loc "traverse" in
    Ast_helper.(
      Sig.value ~loc
      @@ Val.mk
           name
           Typ.(
             arrow Nolabel (ty_con_t @@ var "a")
             @@ arrow
                  (Labelled "f")
                  (arrow Nolabel (var "a") @@ ty_con_A_t @@ var "b")
                  (ty_con_A_t @@ ty_con_t @@ var "b")))
  ;;

  let ap_functor ~loc =
    let name = Ast_builder.Default.Located.mk ~loc @@ Some "Make"
    and type_ =
      Ast_helper.Mty.(
        functor_ Common.(ap_param_base ~loc) (signature [ ap_traverse_fn ~loc ]))
    in
    psig_module ~loc @@ module_declaration ~loc ~name ~type_
  ;;

  let traversable ~ty_name loc _ =
    let name =
      Ast_builder.Default.Located.mk ~loc
      @@ Some Common.(traversable_module ty_name)
    in
    [ psig_module ~loc
      @@ module_declaration
           ~loc
           ~name
           ~type_:(pmty_signature ~loc [ ap_functor ~loc ])
    ]
  ;;

  let traversable_of_td td =
    let ty_name = td.ptype_name.txt in
    let loc = td.ptype_loc in
    traversable ~ty_name loc ()
  ;;

  (* @@ Inspect.type_decl td *)

  let generate ~loc ~path:_ (rec_flag, tds) =
    (match rec_flag with
    | Nonrecursive ->
      Location.raise_errorf
        ~loc
        "nonrec is not compatible with the `ppx_traversable` preprocessor"
    | _ -> ());
    match tds with
    | [ ({ ptype_params = _ :: _; _ } as td) ] -> traversable_of_td td
    | _ -> Location.raise_errorf ~loc "ppx_traversable: not supported"
  ;;
end

module Gen_str = struct

  let ap_return ~loc x = Ast_helper.(
    Exp.(apply 
      (ident @@ Located.mk ~loc @@ Ldot (Lident "A", "return"))
                [ Nolabel , x]
                
    )
  )

  let rec traverse_ty ~var ~k ty =
    match ty.ptyp_desc with
    | Ptyp_var lbl when String.equal lbl var -> (??)

      | Ptyp_arrow (_, _, _) -> (??)
      | Ptyp_tuple _ -> (??)
      | Ptyp_constr (_, _) -> (??)
      | Ptyp_object (_, _) -> (??)
      | Ptyp_class (_, _) -> (??)
      | Ptyp_alias (_, _) -> (??)

      | Ptyp_any -> (??)
      | Ptyp_variant (_, _, _) -> (??)
      | Ptyp_poly (_, _) -> (??)
      | Ptyp_package _ -> (??)
      | Ptyp_extension _ -> (??)

  let rec traverse_tuple ~var ~k = function 
    | [] -> k [] 
    | ty::tys -> 
    Ast_helper.Exp.tuple

  let  partition_on  = 
    let rec aux (xs,ys) = function 
    | ty::tys -> (
      match ty.ptyp_desc with
   
      | Ptyp_var _ -> (??)

      | Ptyp_arrow (_, _, _) -> (??)
      | Ptyp_tuple _ -> (??)
      | Ptyp_constr (_, _) -> (??)
      | Ptyp_object (_, _) -> (??)
      | Ptyp_class (_, _) -> (??)
      | Ptyp_alias (_, _) -> (??)

      | Ptyp_any -> (??)
      | Ptyp_variant (_, _, _) -> (??)
      | Ptyp_poly (_, _) -> (??)
      | Ptyp_package _ -> (??)
      | Ptyp_extension _ -> (??)
      )
        
    | [] -> (xs,ys)

  let ap_ctr_expr lid expr_opt = 
    Ast_helper.Exp.construct lid expr_opt

  let ap_traverse_case ~loc ctr_decl = 
    match ctr_decl.pcd_args with 
    | Pcstr_tuple [] -> 
        let lid = Located.map_lident ctr_decl.pcd_name in 
        ap_return ~loc @@ ap_ctr_expr lid None 

    (* for a tuple, extract arguments in the type we are mapping over *)
    | Pcstr_tuple tys -> 
        let (xs,ys) = partition_on tys in 
        failwith ""
    | Pcstr_record _ -> failwith ""

  let ap_traverse_fn ~loc td =
    match td.ptype_kind with
    | Ptype_variant _ ->
      Ast_helper.(
        Str.value
          Recursive
          Vb.
            [ mk Pat.(var @@ Located.mk ~loc "traverse")
              @@ Exp.fun_ Nolabel None Pat.(var @@ Located.mk ~loc "t")
              @@ Exp.fun_ (Labelled "f") None Pat.(var @@ Located.mk ~loc "f")
              @@ Exp.(apply 
                (ident @@ Located.mk ~loc @@ Ldot (Lident "A", "return"))
                [ Nolabel , ident
                  @@ Located.mk ~loc
                  @@ Lident "t"
                ]
              )
            ])
    | _ -> raise_unsupported loc
  ;;

  let ap_functor ~loc td =
    let name = Located.mk ~loc @@ Some "Make" in
    pstr_module ~loc
    @@ module_binding
         ~loc
         ~name
         ~expr:
           Ast_helper.Mod.(
             functor_
               Common.(ap_param_base ~loc)
               (structure [ ap_traverse_fn ~loc td ]))
  ;;

  let traversable ~ty_name loc td =
    let name = Located.mk ~loc @@ Some Common.(traversable_module ty_name) in
    [ pstr_module ~loc
      @@ module_binding
           ~loc
           ~name
           ~expr:(pmod_structure ~loc [ ap_functor ~loc td ])
    ]
  ;;

  let traversable_of_td td =
    let ty_name = td.ptype_name.txt in
    let loc = td.ptype_loc in
    traversable ~ty_name loc td
  ;;

  let generate ~loc ~path:_ (rec_flag, tds) =
    (match rec_flag with
    | Nonrecursive ->
      Location.raise_errorf
        ~loc
        "nonrec is not compatible with the `ppx_traversable` preprocessor"
    | _ -> ());
    match tds with
    | [ ({ ptype_params = _ :: _; _ } as td) ] -> traversable_of_td td
    | _ -> Location.raise_errorf ~loc "ppx_traversable: not supported"
  ;;
end

let traversable =
  Deriving.add
    "traversable"
    ~str_type_decl:(Deriving.Generator.make_noarg Gen_str.generate)
    ~sig_type_decl:(Deriving.Generator.make_noarg Gen_sig.generate)
;;
