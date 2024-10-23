(** This module implements a bidirectional type checker for Hopix. *)

open HopixAST
open HopixASTHelper

(** Error messages *)

let invalid_instantiation pos given expected =
  HopixTypes.type_error pos (
      Printf.sprintf
        "Invalid number of types in instantiation: \
         %d given while %d were expected." given expected
    )

let check_equal_types pos ~expected ~given =
  if expected <> given
  then
    HopixTypes.(type_error pos
                  Printf.(sprintf
                            "Type mismatch.\nExpected:\n  %s\nGiven:\n  %s"
                            (string_of_aty expected)
                            (string_of_aty given)))


(** Linearity-checking code for patterns *)

let rec check_pattern_linearity
        : identifier list -> pattern Position.located -> identifier list
  = fun vars Position.{ value; position; } ->
  failwith "todo check_pattern_linearity"


(** Util *)

let remove_pos ls =
  let rec aux ls ls_no_pos =
    match ls with 
    | [] -> ls_no_pos
    | Position.({value;position})::tl ->
    aux tl (value :: ls_no_pos)
  in
  aux ls []


let remove_label ls =
  let rec aux ls ls_no_label =
    match ls with
    | [] -> ls_no_label
    | (LId s)::tl -> aux tl (s::ls_no_label)
  in
  aux ls []


(** Type-checking code *)

let check_type_scheme :
      HopixTypes.typing_environment ->
      Position.t ->
      HopixAST.type_scheme ->
      HopixTypes.aty_scheme * HopixTypes.typing_environment
  = fun env pos (ForallTy (ts, ty)) ->
  
    let new_env = HopixTypes.bind_type_variables pos env (remove_pos ts) in

    let internalized_aty = HopixTypes.internalize_ty new_env ty in
	
    ((Scheme((remove_pos ts), internalized_aty)), new_env)


let synth_literal : HopixAST.literal -> HopixTypes.aty =
  fun l -> match l with
  | LInt _    -> ATyCon(TCon ("int"), [])
  | LString _ -> ATyCon(TCon ("string"), [])
  | LChar _   -> ATyCon(TCon ("char"), [])


let rec check_pattern :
          HopixTypes.typing_environment ->
          HopixAST.pattern Position.located ->
          HopixTypes.aty ->
          HopixTypes.typing_environment
  = fun env Position.({ value = p; position = pos; } as pat) expected ->
  match p with
  | PVariable id -> 
    let ats = HopixTypes.generalize_type env expected in
    HopixTypes.bind_value (Position.value id) ats env 
  | PWildcard -> env
  | PTypeAnnotation (pa,ty) -> 

    let (given,env2) = synth_pattern env pat in
    check_equal_types pos ~expected:expected ~given:given;
    env2
  
  | PLiteral lit -> 
    check_equal_types
      pos
      ~expected:expected
      ~given:(synth_literal (Position.value lit));
    env

  | PTaggedValue (cons,ty_ls_opt,p_ls) -> 

    (try (
    let Scheme(ty_var_ls,aty) = HopixTypes.lookup_type_scheme_of_constructor
      (Position.position cons) (Position.value cons) env in
      
    (match ty_ls_opt with
    | None -> 
      failwith "none"
    | Some ty_ls -> 

      let tau_ls = List.map (fun ty ->
        ( HopixTypes.internalize_ty env ty)) (ty_ls) in

      (* val instantiate_type_scheme : aty_scheme -> aty list -> aty *)
      (*
      let aty' = HopixTypes.instantiate_type_scheme (Scheme(ty_var_ls,aty)) (tau_ls) in
      *)

      if (List.length p_ls) <> (List.length tau_ls) then failwith "wrong arity"
      else
      List.fold_left2 (fun env p aty -> 
        ( check_pattern env p aty )) (env) (p_ls) (tau_ls)))

  with HopixTypes.Unbound (pos, id) -> 
    HopixTypes.type_error pos ("Unbound " ^ (HopixTypes.string_of_binding id) ^ "."))


  | PRecord (ls,ty_ls_opt) ->
    failwith "check_pattern precord"

  | PTuple (p_ls) ->
    (* Jugement CheckPTuple *)
    let aty_ls = HopixTypes.destruct_product_type pos expected in

    let rec check_pat_aux env p_ls aty_ls =
      match p_ls,aty_ls with
      | (x::xs, y::ys) ->
        let env2 = check_pattern env x y in
        check_pat_aux env2 xs ys
      | ([],[]) -> env
      | (_,_) -> failwith "wrong arity"
    in

    (check_pat_aux env p_ls aty_ls)

  | POr (p_ls) ->
    List.fold_left (fun env p -> 
      ( check_pattern env p expected )) (env) (p_ls)
  | PAnd (p_ls) ->
    List.fold_left (fun env p -> 
      ( check_pattern env p expected )) (env) (p_ls);


and synth_pattern :
      HopixTypes.typing_environment ->
      HopixAST.pattern Position.located ->
      HopixTypes.aty * HopixTypes.typing_environment
  = fun env Position.{ value = p; position = pos; } ->
  match p with
  | PVariable id -> failwith "synth_pattern pvariable"
  | PWildcard -> failwith "synth_pattern pwildcard"
  | PTypeAnnotation (pa,ty) -> 
    (* Jugement PAnnot *)
    let tau = HopixTypes.internalize_ty env ty in
    let env2 = check_pattern env pa tau in
    (tau,env2)

  | PLiteral lit -> 
    failwith "synth_pattern pliteral"
  | PTaggedValue (cons,ty_ls_opt,p_ls) -> 

    failwith "synth_pattern ptaggedvalue"

  | PRecord (ls,ty_ls_opt) ->
    failwith "synth_pattern precord"
  
  | PTuple (p_ls) ->

    let (aty_ls, env') = 
      List.fold_left (fun (aty_ls,env) p -> 
        (let (aty,env') = (synth_pattern env p) in 
        ((aty::aty_ls),env'))) ([],env) (p_ls) in
    
    ( ATyTuple (List.rev aty_ls) , env' )

  | POr (p_ls) -> failwith "synth_pattern por"
  | PAnd (p_ls) -> failwith "synth_pattern pand"


let rec synth_expression :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixTypes.aty
  = fun env Position.{ value = e; position = pos; } ->
  match e with
  | Literal lit -> synth_literal (Position.value lit)

  | Variable(id,ty_ls) ->
    (match ty_ls with
    | Some ls -> 

      let aty_ls = List.map (fun ty -> 
        (HopixTypes.internalize_ty env ty)) (ls) in

      let (Scheme (ts, ty)) = HopixTypes.lookup_type_scheme_of_identifier 
        (Position.position id) (Position.value id) env in

      HopixTypes.instantiate_type_scheme (Scheme (ts, ty)) aty_ls
      
    | None -> 
      (* TODO [KO] 10-local-definition.bad *)
      try 
        (let Scheme(ty_var_ls,aty) = HopixTypes.lookup_type_scheme_of_identifier 
          (Position.position id) (Position.value id) env in
        
          if ((List.length ty_var_ls) <> 0 ) 
          then HopixTypes.type_error pos "Type error"
          else aty)
      with HopixTypes.Unbound (pos, id) -> 
        HopixTypes.type_error pos ("Unbound " ^ (HopixTypes.string_of_binding id) ^ "."))
    
  | Tagged(c,ty_ls_opt,e_list) ->

    (match ty_ls_opt with
    | None -> failwith "todo synth_expression tagged none"
    | Some ty_ls -> 
      
      let tau_ls = List.map (fun ty -> 
        ( HopixTypes.internalize_ty env ty )) (ty_ls) in
    
      try (
        let ts = HopixTypes.lookup_type_scheme_of_constructor 
          (Position.position c) (Position.value c) env in
        
        let ts_instance = HopixTypes.instantiate_type_scheme ts tau_ls in

        ts_instance)
      with HopixTypes.Unbound (pos, id) -> 
        HopixTypes.type_error pos ("Unbound " ^ (HopixTypes.string_of_binding id) ^ "."))
      

  | Record(field_ls,ty_ls_opt) ->
    
    (match ty_ls_opt with
    | None -> failwith "todo synth_expression record : ty located list option = None"
    | Some ty_ls -> 
      let aty_ls = List.map 
        (fun ty -> (HopixTypes.internalize_ty env ty)) (ty_ls) in
      
      let fst_field = Position.value (fst (List.hd field_ls)) in
      
      let ((TCon constr),n,label_ls) = HopixTypes.lookup_type_constructor_of_label pos fst_field env in 

      let field_ls_sorted = List.split (List.sort 
        (fun  ((Position.{ value = (LId s1); position = pos1 }),e1)
              ((Position.{ value = (LId s2); position = pos2 }),e2) -> 
          ( String.compare s1 s2 )) (field_ls)) in
      
      let field_ls_sorted' = List.combine
        (fst field_ls_sorted) (snd field_ls_sorted) in
      
      let label_ls_sorted = List.sort (fun (LId s1) (LId s2) -> 
        ( String.compare s1 s2 )) (label_ls) in
      

      if (List.length (fst field_ls_sorted)) <> (List.length label_ls_sorted)
      then failwith "wrong arity" else

      (* iterate on both lists to check the type of each field *)
      List.iter2 (fun ((Position.{ value = (LId l1); position = pos1 }),e1) (LId l2) -> 
        ( if l1 <> l2 then failwith ("unbound field " ^ l1) else

          let aty_sch = HopixTypes.lookup_type_scheme_of_label pos (LId l2) env in
          
          let ts_instance = HopixTypes.instantiate_type_scheme aty_sch aty_ls in

          check_expression env e1 ts_instance
          
        )) (field_ls_sorted') (label_ls_sorted);

      ATyCon ((TCon constr),aty_ls))

  | Field(e,l,ty_ls_opt) ->
    failwith "todo synth_expression field"
  
  | Tuple(e_ls) ->
    ATyTuple ( List.map (fun exp -> (synth_expression env exp)) e_ls )

  | Sequence(e_ls) ->
    failwith "todo synth_expression sequence"

  | Define(vd,exp) ->
    (* JUGEMENT SYNTHLET *)
    let env2 = check_value_definition env vd in
    synth_expression env2 exp
  
  | Fun(FunctionDefinition(pat,exp)) ->
    (* JUGEMENT SYNTHFUN *)
    let (ty_pat,env2) = synth_pattern env pat in
    let ty_exp = synth_expression env2 exp in
    ATyArrow( ty_pat , ty_exp)
  
  | Apply(e1,e2) ->
    let ty_e1 = synth_expression env e1 in
    let (t1,t2) = HopixTypes.destruct_function_type (Position.position e1) ty_e1 in
    check_expression env e2 t1; t2

  | Ref(e) ->
    failwith "todo synth_expression ref"
  
  | Assign(e1,e2) ->

    let ty_e1 = synth_expression env e1 in
    let t1 = HopixTypes.destruct_reference_type (Position.position e1) ty_e1 in
    check_expression env e2 t1;
    HopixTypes.hunit
  
  | Read(exp) ->
    let ty = synth_expression env exp in
    let t = HopixTypes.destruct_reference_type (Position.position exp) ty in t
  
  | Case(e,b_ls) ->
    failwith "todo synth_expression case"

  | IfThenElse(e1,e2,e3) ->
    let ty_e1 = synth_expression env e1 in
    check_equal_types (Position.position e1) ~expected:HopixTypes.hbool ~given:ty_e1;
    let ty_e2 = synth_expression env e2 in
    check_expression env e3 ty_e2; ty_e2

  | While(e1,e2) ->
    let ty_e1 = synth_expression env e1 in
    check_equal_types (Position.position e1) ~expected:HopixTypes.hbool ~given:ty_e1;
    let ty_e2 = synth_expression env e2 in
    check_equal_types (Position.position e2) ~expected:HopixTypes.hunit ~given:ty_e2;
    HopixTypes.hunit

  | For(id,e1,e2,e3) ->
    let ty_e1 = synth_expression env e1 in
    check_equal_types (Position.position e1) ~expected:HopixTypes.hint ~given:ty_e1;
    let ty_e2 = synth_expression env e2 in
    check_equal_types (Position.position e2) ~expected:HopixTypes.hint ~given:ty_e2;
    let ty_e3 = synth_expression env e3 in
    check_equal_types (Position.position e3) ~expected:HopixTypes.hunit ~given:ty_e3;
    HopixTypes.hunit

  | TypeAnnotation(exp,ty) ->
    (* Jugement SynthAnnot *)
    let tau = HopixTypes.internalize_ty env ty in
    check_expression env exp tau; tau


and check_expression :
      HopixTypes.typing_environment ->
      HopixAST.expression Position.located ->
      HopixTypes.aty ->
      unit
  = fun env (Position.{ value = e; position = pos; } as exp) expected ->

    match e with 
    | Literal _ | Tagged (_,_,_) | Apply (_,_) | Variable (_,_) | Read _ | Assign (_,_) 
    | While (_,_) | For (_,_,_,_) | TypeAnnotation (_,_) | Record (_,_) | Tuple _ ->
      let given = synth_expression env exp in
      check_equal_types pos ~expected:expected ~given:given
    
    | Field(e,l,ty_ls_opt) ->
      (match ty_ls_opt with
      | None -> failwith "check_expression field None"
      | Some ty_ls -> 
        let aty_sch = HopixTypes.lookup_type_scheme_of_label 
          (Position.position l) (Position.value l) env in

        let aty_ls = List.map 
          (fun ty -> (HopixTypes.internalize_ty env ty)) (ty_ls) in

        let given = HopixTypes.instantiate_type_scheme aty_sch aty_ls in

        check_equal_types pos ~expected:expected ~given:given)
    
    | Sequence(e_ls) ->
      let rec iter_seq e_ls = 
        match e_ls with
        | exp::[] ->
          let given = synth_expression env exp in
          check_equal_types pos ~expected:expected ~given:given
        | exp::tl ->
          let given = synth_expression env exp in
          check_equal_types pos ~expected:(HopixTypes.hunit) ~given:given;
          iter_seq tl
      in iter_seq e_ls

    | Define(vd,e) ->
      (* JUGEMENT CHECKLET *)
      let env2 = check_value_definition env vd in
      check_expression env2 e expected

    | Fun(FunctionDefinition(pat,exp)) ->
      (* JUGEMENT CHECKFUN *)
      let (tau,tau2) = HopixTypes.destruct_function_type pos expected in
      let env2 = check_pattern env pat tau in
      check_expression env2 exp tau2;

    | Ref(exp) ->
      let ty_e = synth_expression env exp in
      let given = HopixTypes.href ty_e in
      check_equal_types pos ~expected:expected ~given:given
    
    | Case(e,b_ls) ->
      (* JUGEMENT CHECKMATCH *)
      let ty_e = synth_expression env e in
      List.iter 
        (fun b -> check_branch env ty_e expected (Position.value b)) b_ls

    | IfThenElse(e1,e2,e3) ->
      failwith "todo check_expression if then else"


and check_branch :
      HopixTypes.typing_environment ->
      HopixTypes.aty ->
      HopixTypes.aty ->
      HopixAST.branch ->
      unit
  = fun env ty_matched ty_res (Branch (pat, exp)) -> 
  
  (* Vérification que le pattern de la branche filtre les motifs de type ty_matched *)
  let env2 = check_pattern env pat ty_matched in
  
  (* Vérification que le type du corps exp de la branche est du type ty_res *)
  check_expression env2 exp ty_res


and synth_branch :
      HopixTypes.typing_environment ->
      HopixTypes.aty ->
      HopixAST.branch ->
      HopixTypes.aty
  = fun env ty_matched (Branch (pat, exp)) -> 
  
  let env2 = check_pattern env pat ty_matched in
  synth_expression env2 exp


and check_value_definition :
      HopixTypes.typing_environment ->
      HopixAST.value_definition ->
      HopixTypes.typing_environment
  = fun env def ->
    
    match def with
    
    (* SimpleValue of expression located polymorphic_definition *)
    | SimpleValue ((Position.{ value = id_val; position = id_pos }), ts_opt, expr) ->
      
      (match ts_opt with
      | None -> 

        let aty_synth = synth_expression env expr in
        let (Scheme (ty_var_ls, ty)) = HopixTypes.generalize_type env aty_synth in
        
        HopixTypes.bind_value id_val (Scheme(ty_var_ls, ty)) env

      | Some (Position.{ value = (ForallTy(alpha_ls,tau) as ts_val); position = ts_pos }) ->
        
        (* Check type scheme *)
        let ((Scheme (ty_var_ls, ty)), ty_env) = check_type_scheme env ts_pos ts_val in
        (* Check expression *)
        check_expression ty_env expr ty;
        (* Return the extended environment *)
        HopixTypes.bind_value id_val (Scheme(ty_var_ls,ty)) ty_env)
    
    (* RecFunctions of function_definition polymorphic_definition list *)
    | RecFunctions fundef_ls ->

      let env' = List.fold_left (fun env (id, ts_opt, FunctionDefinition(pat,exp)) -> 
        (match ts_opt with
        | None -> failwith "Toutes les fonctions doivent etre annotées."
        | Some ts -> 

          (* Pour typer des fonctions mutuellement récursives, on commence par vérifier 
          que les annotations de types écrites par l'utilisateur sont bien formées. *)
          let ((Scheme (ty_var_ls', ty')), ty_env) = 
            check_type_scheme env (Position.position ts) (Position.value ts) in

          (* On produit l’environnement Γ′ dans lequel les fonctions f sont associées à leurs types *)
          HopixTypes.bind_value (Position.value id) (Scheme (ty_var_ls', ty')) env

          )) (env) (fundef_ls) in
      
      (* On vérifie qu’effectivement les définitions de ces fonctions sont bien du type annoté par le programmeur. *)
      List.iter (fun (id, ts_opt, FunctionDefinition(pat,exp)) -> 
        (match ts_opt with
        | None -> failwith "Toutes les fonctions doivent etre annotées."
        | Some (Position.{ value = (ForallTy(ty_var_ls,ty)); position = ts_pos }) ->

          try(
            let Scheme(ty_var_ls',aty) = 
              HopixTypes.lookup_type_scheme_of_identifier (Position.position id) (Position.value id) env' in
        
            (* Ajout des variables de type à l'environnement *)
            let env2 = HopixTypes.bind_type_variables (ts_pos) (env') (ty_var_ls') in
            
            let (aty_pat', aty_exp') = HopixTypes.destruct_function_type ts_pos aty in
            
            let env3 = check_pattern env2 pat aty_pat' in
            
            check_expression env3 exp aty_exp')
          
          with HopixTypes.Unbound (pos, id) -> 
            HopixTypes.type_error pos ("Unbound " ^ (HopixTypes.string_of_binding id) ^ ".")
          ) ) (fundef_ls);

      env'


let check_definition env = function
  | DefineValue vdef ->
     check_value_definition env vdef

  | DefineType (t, ts, tdef) ->
     let ts = List.map Position.value ts in
     HopixTypes.bind_type_definition (Position.value t) ts tdef env

  | DeclareExtern (x, tys) ->
     let tys, _ = Position.located_pos (check_type_scheme env) tys in
     HopixTypes.bind_value (Position.value x) tys env

let typecheck env program =
  List.fold_left
    (fun env d -> Position.located (check_definition env) d)
    env program

type typing_environment = HopixTypes.typing_environment

let initial_typing_environment = HopixTypes.initial_typing_environment

let print_typing_environment = HopixTypes.string_of_typing_environment
