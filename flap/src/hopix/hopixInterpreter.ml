open Position
open Error
open HopixAST

(** [error pos msg] reports execution error messages. *)
let error positions msg =
  errorN "execution" positions msg

(** Every expression of Hopix evaluates into a [value].

   The [value] type is not defined here. Instead, it will be defined
   by instantiation of following ['e gvalue] with ['e = environment].
   Why? The value type and the environment type are mutually recursive
   and since we do not want to define them simultaneously, this
   parameterization is a way to describe how the value type will use
   the environment type without an actual definition of this type.

*)
type 'e gvalue =
  | VInt       of Mint.t
  | VChar      of char
  | VString    of string
  | VUnit
  | VTagged    of constructor * 'e gvalue list
  | VTuple     of 'e gvalue list
  | VRecord    of (label * 'e gvalue) list
  | VLocation  of Memory.location
  | VClosure   of 'e * pattern located * expression located
  | VPrimitive of string * ('e gvalue Memory.t -> 'e gvalue -> 'e gvalue)

(** Two values for booleans. *)
let ptrue  = VTagged (KId "True", [])
let pfalse = VTagged (KId "False", [])

(**
    We often need to check that a value has a specific shape.
    To that end, we introduce the following coercions. A
    coercion of type [('a, 'e)] coercion tries to convert an
    Hopix value into a OCaml value of type ['a]. If this conversion
    fails, it returns [None].
*)

type ('a, 'e) coercion = 'e gvalue -> 'a option
let fail = None
let ret x = Some x
let value_as_int      = function VInt x -> ret x | _ -> fail
let value_as_char     = function VChar c -> ret c | _ -> fail
let value_as_string   = function VString s -> ret s | _ -> fail
let value_as_tagged   = function VTagged (k, vs) -> ret (k, vs) | _ -> fail
let value_as_record   = function VRecord fs -> ret fs | _ -> fail
let value_as_location = function VLocation l -> ret l | _ -> fail
let value_as_closure  = function VClosure (e, p, b) -> ret (e, p, b) | _ -> fail
let value_as_primitive = function VPrimitive (p, f) -> ret (p, f) | _ -> fail
let value_as_bool = function
  | VTagged (KId "True", []) -> true
  | VTagged (KId "False", []) -> false
  | _ -> assert false

(**
   It is also very common to have to inject an OCaml value into
   the types of Hopix values. That is the purpose of a wrapper.
 *)
type ('a, 'e) wrapper = 'a -> 'e gvalue
let int_as_value x  = VInt x
let bool_as_value b = if b then ptrue else pfalse

(**

  The flap toplevel needs to print the result of evaluations. This is
   especially useful for debugging and testing purpose. Do not modify
   the code of this function since it is used by the testsuite.

*)
let print_value m v =
  (** To avoid to print large (or infinite) values, we stop at depth 5. *)
  let max_depth = 5 in

  let rec print_value d v =
    if d >= max_depth then "..." else
      match v with
        | VInt x ->
          Mint.to_string x
        | VChar c ->
          "'" ^ Char.escaped c ^ "'"
        | VString s ->
          "\"" ^ String.escaped s ^ "\""
        | VUnit ->
          "()"
        | VLocation a ->
          print_array_value d (Memory.dereference m a)
        | VTagged (KId k, []) ->
          k
        | VTagged (KId k, vs) ->
          k ^ print_tuple d vs
        | VTuple (vs) ->
           print_tuple d vs
        | VRecord fs ->
           "{"
           ^ String.concat ", " (
                 List.map (fun (LId f, v) -> f ^ " = " ^ print_value (d + 1) v
           ) fs) ^ "}"
        | VClosure _ ->
          "<fun>"
        | VPrimitive (s, _) ->
          Printf.sprintf "<primitive: %s>" s
    and print_tuple d vs =
      "(" ^ String.concat ", " (List.map (print_value (d + 1)) vs) ^ ")"
    and print_array_value d block =
      let r = Memory.read block in
      let n = Mint.to_int (Memory.size block) in
      "[ " ^ String.concat ", " (
                 List.(map (fun i -> print_value (d + 1) (r (Mint.of_int i)))
                         (ExtStd.List.range 0 (n - 1))
               )) ^ " ]"
  in
  print_value 0 v

let print_values m vs =
  String.concat "; " (List.map (print_value m) vs)

module Environment : sig
  (** Evaluation environments map identifiers to values. *)
  type t

  (** The empty environment. *)
  val empty : t

  (** [bind env x v] extends [env] with a binding from [x] to [v]. *)
  val bind    : t -> identifier -> t gvalue -> t

  (** [update pos x env v] modifies the binding of [x] in [env] so
      that [x ↦ v] ∈ [env]. *)
  val update  : Position.t -> identifier -> t -> t gvalue -> unit

  (** [lookup pos x env] returns [v] such that [x ↦ v] ∈ env. *)
  val lookup  : Position.t -> identifier -> t -> t gvalue

  (** [UnboundIdentifier (x, pos)] is raised when [update] or
      [lookup] assume that there is a binding for [x] in [env],
      where there is no such binding. *)
  exception UnboundIdentifier of identifier * Position.t

  (** [last env] returns the latest binding in [env] if it exists. *)
  val last    : t -> (identifier * t gvalue * t) option

  (** [print env] returns a human readable representation of [env]. *)
  val print   : t gvalue Memory.t -> t -> string
end = struct

  type t =
    | EEmpty
    | EBind of identifier * t gvalue ref * t

  let empty = EEmpty

  let bind e x v =
    EBind (x, ref v, e)

  exception UnboundIdentifier of identifier * Position.t

  let lookup' pos x =
    let rec aux = function
      | EEmpty -> raise (UnboundIdentifier (x, pos))
      | EBind (y, v, e) ->
        if x = y then v else aux e
    in
    aux

  let lookup pos x e = !(lookup' pos x e)

  let update pos x e v =
    lookup' pos x e := v

  let last = function
    | EBind (x, v, e) -> Some (x, !v, e)
    | EEmpty -> None

  let print_binding m (Id x, v) =
    x ^ " = " ^ print_value m !v

  let print m e =
    let b = Buffer.create 13 in
    let push x v = Buffer.add_string b (print_binding m (x, v)) in
    let rec aux = function
      | EEmpty -> Buffer.contents b
      | EBind (x, v, EEmpty) -> push x v; aux EEmpty
      | EBind (x, v, e) -> push x v; Buffer.add_string b "\n"; aux e
    in
    aux e

end

(**
    We have everything we need now to define [value] as an instantiation
    of ['e gvalue] with ['e = Environment.t], as promised.
*)
type value = Environment.t gvalue

(**
   The following higher-order function lifts a function [f] of type
   ['a -> 'b] as a [name]d Hopix primitive function, that is, an
   OCaml function of type [value -> value].
*)
let primitive name ?(error = fun () -> assert false) coercion wrapper f
: value
= VPrimitive (name, fun x ->
    match coercion x with
      | None -> error ()
      | Some x -> wrapper (f x)
  )

type runtime = {
  memory      : value Memory.t;
  environment : Environment.t;
}

type observable = {
  new_memory      : value Memory.t;
  new_environment : Environment.t;
}

(** [primitives] is an environment that contains the implementation
    of all primitives (+, <, ...). *)
let primitives =
  let intbin name out op =
    let error m v =
      Printf.eprintf
        "Invalid arguments for `%s': %s\n"
        name (print_value m v);
      assert false (* By typing. *)
    in
    VPrimitive (name, fun m -> function
      | VInt x ->
         VPrimitive (name, fun m -> function
         | VInt y -> out (op x y)
         | v -> error m v)
      | v -> error m v)
  in
  let bind_all what l x =
    List.fold_left (fun env (x, v) -> Environment.bind env (Id x) (what x v))
      x l
  in
  (* Define arithmetic binary operators. *)
  let binarith name =
    intbin name (fun x -> VInt x) in
  let binarithops = Mint.(
    [ ("`+`", add); ("`-`", sub); ("`*`", mul); ("`/`", div) ]
  ) in
  (* Define arithmetic comparison operators. *)
  let cmparith name = intbin name bool_as_value in
  let cmparithops =
    [ ("`=?`", ( = ));
      ("`<?`", ( < ));
      ("`>?`", ( > ));
      ("`>=?`", ( >= ));
      ("`<=?`", ( <= )) ]
  in
  let boolbin name out op =
    VPrimitive (name, fun _ x -> VPrimitive (name, fun _ y ->
        out (op (value_as_bool x) (value_as_bool y))))
  in
  let boolarith name = boolbin name (fun x -> if x then ptrue else pfalse) in
  let boolarithops =
    [ ("`||`", ( || )); ("`&&`", ( && )) ]
  in
  let generic_printer =
    VPrimitive ("print", fun m v ->
      output_string stdout (print_value m v);
      flush stdout;
      VUnit
    )
  in
  let print s =
    output_string stdout s;
    flush stdout;
    VUnit
  in
  let print_int =
    VPrimitive  ("print_int", fun _ -> function
      | VInt x -> print (Mint.to_string x)
      | _ -> assert false (* By typing. *)
    )
  in
  let print_string =
    VPrimitive  ("print_string", fun _ -> function
      | VString x -> print x
      | _ -> assert false (* By typing. *)
    )
  in
  let bind' x w env = Environment.bind env (Id x) w in
  Environment.empty
  |> bind_all binarith binarithops
  |> bind_all cmparith cmparithops
  |> bind_all boolarith boolarithops
  |> bind' "print"        generic_printer
  |> bind' "print_int"    print_int
  |> bind' "print_string" print_string
  |> bind' "true"         ptrue
  |> bind' "false"        pfalse
  |> bind' "nothing"      VUnit

let initial_runtime () = {
  memory      = Memory.create (640 * 1024 (* should be enough. -- B.Gates *));
  environment = primitives;
}

let rec evaluate runtime ast =
  try
    let runtime' = List.fold_left definition runtime ast in
    (runtime', extract_observable runtime runtime')
  with Environment.UnboundIdentifier (Id x, pos) ->
    Error.error "interpretation" pos (Printf.sprintf "`%s' is unbound." x)


(** [definition runtime d] evaluates the new definition [d]
    into a new runtime [runtime']. In the specification, this
    is the judgment:

                        E, M ⊢ dv ⇒ E', M'

*)
and definition runtime d =

  match (value d) with
  | DefineType (_,_,_) -> runtime
  | DeclareExtern (_,_) -> runtime
  | DefineValue vd -> 
    
    match vd with
    | SimpleValue (id, _, expr) -> 

      let expr_gvalue = 
        expression' runtime.environment runtime.memory expr in
      
      (* Runtime with a new environment in which the identifier id is bound to expr *)
      { environment = (update_env runtime.environment id expr_gvalue) ; memory = runtime.memory }

    | RecFunctions fundef_ls -> 

      let rec update_bindings new_env mem l1 l2 =
        match l1 with
        | [] -> {environment=new_env; memory=mem}
        | (id,_,_)::tl ->
          Environment.update (position id) (value id) new_env (List.hd l2);
          update_bindings new_env mem tl (List.tl l2)
      in

      let rec eval_fundef new_env mem l1 l2 =
        match l1 with
        | [] -> l2
        | (_,_,fundef)::tl ->
          eval_fundef new_env mem tl (( expression' new_env mem (Position.unknown_pos (Fun(fundef))) ) :: l2)
      in

      let rec bind_ids env mem ls =
        match ls with
        | [] -> env
        | (id,_,_)::tl ->
          bind_ids (update_env env id VUnit) mem tl
      in

      let new_env = bind_ids runtime.environment runtime.memory fundef_ls in
      let fun_ls = eval_fundef new_env runtime.memory fundef_ls [] in

      update_bindings new_env runtime.memory fundef_ls fun_ls


and expression' environment memory e =
  expression (position e) environment memory (value e)


(** [expression pos environment memory e] evaluates into a value [v] if

                          E, M ⊢ e ⇓ v, M'

   and E = [runtime.environment], M = [runtime.memory].
*)
and expression _ environment memory e =

  let eval_expr_list expr_list =
    
    let rec eval_aux val_list gval_list =
      match val_list with
      | [] -> List.rev gval_list
      | x::tl -> 
          
      let x_gval = expression' environment memory x in
          
      eval_aux (tl) (x_gval :: gval_list)
    in

    eval_aux expr_list []

  in

  match e with
  | Literal lit -> 
    
    (match (value lit) with
    | LInt n -> VInt n
    | LChar c -> VChar c
    | LString s -> VString s)

  | Variable (id, _) -> 
    Environment.lookup (Position.position id) (Position.value id) (environment)
  
  | Tagged (constr, _, expr_list) ->
    VTagged ((Position.value constr), (eval_expr_list expr_list))
  
  | Record (ls, _) ->
    let ls_split = List.split ls in

    let rec extract_value_ls ls res =
      match ls with
      | [] -> List.rev res
      | x::tl -> 
        extract_value_ls (tl) ((Position.value x)::res)
    in

    let ls_combined =
      List.combine 
      (extract_value_ls (fst ls_split) [])
      (eval_expr_list (snd ls_split))
    in

    VRecord ls_combined
  
  | Field (expr, lid, _) ->
    let expr_eval = expression' environment memory expr in

    let rec eval_field ls lid =
      match ls with
      | [] -> 
        failwith "No field with the expected label"
      | (lab, gval)::tl ->
        if lid = lab then gval
        else eval_field tl lid
    in
    
    (match expr_eval with
    | VRecord ls -> eval_field ls (value lid)
    | _ -> failwith "Expected type VRecord")

  | Tuple (expr_list) -> VTuple (eval_expr_list expr_list)

  | Sequence (expr_list) -> 
    
    let rec eval_seq seq =
      match seq with
      | []    -> failwith "empty sequence"
      | x::tl -> 
        let x_gval = expression' environment memory x in
        if (tl = []) then x_gval else eval_seq tl 

    in

    eval_seq expr_list

  | Define (vd, expr) ->
    
    let new_runtime = 
      definition 
        ({ memory = memory ; environment = environment })
        (Position.unknown_pos (DefineValue vd))
    in
    
    expression' new_runtime.environment new_runtime.memory expr

  | Fun ( FunctionDefinition (p, expr)) ->
    VClosure (environment, p, expr)

  | Apply (ef, ea) ->

    let ef_eval = expression' environment memory ef in

    (match ef_eval with
    | VClosure (env_f,p,expr) ->
      let ea_eval = expression' environment memory ea in
      let ea_match_pattern = pattern env_f ea_eval (Position.value p) in

      (match ea_match_pattern with
      | Some new_env  -> expression' new_env memory expr
      | None          -> failwith "Argument is non appliable (does not match the pattern)")

    | VPrimitive (_,primitive_fun) ->
      primitive_fun memory (expression' environment memory ea)

    | _ -> failwith "Expected type VClosure or VPrimitive")

  | Ref (expr) -> 
    
    let v = expression' environment memory expr in

    VLocation (Memory.allocate memory (Mint.one) v)

  | Assign (e1, e2) -> 
    let a = expression' environment memory e1 in
    let v = expression' environment memory e2 in

    (match a with
    | VLocation loc ->
      let blk = Memory.dereference memory loc in
      (Memory.write blk Mint.zero v) ; VUnit
    | _ -> failwith "Expected type VLocation")

  | Read (expr) -> 
    let a = expression' environment memory expr in
    
    (match a with
    | VLocation (location) -> Memory.read (Memory.dereference memory location) Mint.zero
    | _ -> failwith "Expected type VLocation")

  | Case (expr, branch_list) ->

    let expr_eval = expression' environment memory expr in
    branches environment memory expr_eval branch_list

  | IfThenElse (ec, et, ef) ->

    let cond = expression' environment memory ec in

    (match cond with 
    | VTagged (KId "True", []) -> expression' environment memory et
    | VTagged (KId "False", []) -> expression' environment memory ef
    | _ -> failwith "Expected a boolean")

  | While (eb, ebody) ->

    let rec eval_while_loop env mem eb ebody =
      match (expression' environment memory eb) with
      | cond when (cond = ptrue) ->
        let ebody_eval = expression' environment memory ebody in
        eval_while_loop env mem eb ebody

      | cond when (cond = pfalse) -> VUnit
      
      | _ -> failwith "Expected a boolean"
    in

    eval_while_loop environment memory eb ebody

  | For (id, e1, e2, e) ->
    
    let n1 = expression' environment memory e1 in
    let n2 = expression' environment memory e2 in

    let rec eval_for_loop env mem id i1 i2 e =
      if ((Mint.to_int i1) <= (Mint.to_int i2)) then
        let new_env = (update_env env id (VInt i1)) in
        let v = expression' new_env mem e in
        eval_for_loop env mem id (Mint.add i1 Mint.one) i2 e
      else
        VUnit
    in

    (match (n1,n2) with
    | ((VInt i1), (VInt i2)) -> 
      eval_for_loop environment memory id i1 i2 e
    | (_,_) -> failwith "Expected an integer")
  
  | TypeAnnotation (_, _) -> failwith "annotation"



(** This function attempts to match value v with each branch of branch_list sequentially,
    until one of them matches v. *)
and branches environment memory v branch_list = 
  match branch_list with 
  | [] -> failwith "match failure"
  | {value=(Branch (p,e)); position=_}::tl ->
    let pt_match_res = pattern environment v (Position.value p) in
    
    match pt_match_res with
    | Some new_env  -> expression' new_env memory e
    | None          -> branches environment memory v tl



(** pattern : Environment.t -> 'Environment.t gvalue -> pattern -> Environment.t option 
    This function attempts to match the value v with the pattern p, and may modify the
    environment env accordingly if v matches p.
    If v matches p, the function returns Some of env, or None otherwise. *)
and pattern env v p =

  match p with
  | PVariable id -> Some (update_env env id v)

  | PWildcard -> Some env

  | PTypeAnnotation (_,_) ->
    failwith "ptypeannotation"
  
  | PLiteral lit ->
    (match (value lit) with
    | LInt n    -> (match v with
      | VInt m when (n=m)  -> Some env
      | _                  -> None)
    | LString s -> (match v with
      | VString t when (s=t) -> Some env
      | _                    -> None)
    | LChar c   -> (match v with
      | VChar d when (c=d) -> Some env
      | _                  -> None))
    
  | PTaggedValue (c1, _, p_ls) ->
    
    (match v with
    | VTagged (c2, v_ls) -> 
      if ((value c1) <> c2) then None 
      else (cmp_val_ls v_ls p_ls env)
    | _ -> None )
  
  | PRecord (p_ls, _) ->
    
    let p_lex_sort = List.sort
    (fun ({value=LId(x); position=_}, _) ({value=LId(y); position=_}, _) ->
      String.compare x y) (p_ls) in
    let psplit = List.split p_lex_sort in
    
    let rec cmp_label_ls l1 l2 =
      match (l1,l2) with
      | [],[] -> true
      | x::xs,y::ys -> 
        if ((value x) = y) then cmp_label_ls xs ys
        else false
      | (_,_) -> false
    in

    (match v with
    | VRecord v_ls ->

      let v_lex_sort = List.sort(fun (LId(x),_) (LId(y),_) ->
        String.compare x y) (v_ls) in
      let vsplit = List.split v_lex_sort in
      
      if (cmp_label_ls (fst psplit) (fst vsplit)) 
        then (cmp_val_ls (snd vsplit) (snd psplit) env)
      else None

    | _ -> None)

  | PTuple p_ls ->
    (match v with
    | VTuple v_ls -> (cmp_val_ls v_ls p_ls env)
    | _ -> 
      None )
  
  | POr p_ls ->
    
    let rec eval_por env v p_ls =
      match p_ls with
      | []    -> None
      | x::tl -> (match (pattern env v (value x)) with
        | Some new_env -> Some new_env 
        | None -> eval_por env v tl)
    in

    eval_por env v p_ls
  
    | PAnd p_ls ->

    let rec eval_pand env v p_ls =
      match p_ls with
      | []    -> None
      | x::tl -> (match (pattern env v (value x)) with
        | Some new_env ->
          (if (tl = []) then (Some new_env)
          else (eval_pand new_env v tl))
        | None -> None )
    in

    eval_pand env v p_ls



(** This function compares each Environment.t gvalue in list v_ls to the pattern in the
    same position in list p_ls to determine whether each value matches the corresponding pattern. 
    Returns Some of a new environment if all values match their pattern, and None otherwise *)
and cmp_val_ls v_ls p_ls env = 
  match v_ls,p_ls with
  | [],[] -> Some env
  | x::xs,y::ys ->
    (match (pattern env x (value y)) with
    | Some new_env -> cmp_val_ls xs ys new_env
    | None -> None )
  | (_,_) -> None



(** update_env : Environment.t -> identifier located -> 'Environment.t gvalue 
    This function binds the identifier id to the value gval in the environment env.
    It overrides the existing binding of if it already exists, or creates a new one otherwise. *)
and update_env env id gval =
  try 
    ((Environment.update (Position.position id) (Position.value id) env gval) ; env)
  with Environment.UnboundIdentifier (_,_) ->
    (Environment.bind env (Position.value id) gval)


(** This function returns the difference between two runtimes. *)
and extract_observable runtime runtime' =
  let rec substract new_environment env env' =
    if env == env' then new_environment
    else
      match Environment.last env' with
        | None -> assert false (* Absurd. *)
        | Some (x, v, env') ->
          let new_environment = Environment.bind new_environment x v in
          substract new_environment env env'
  in
  {
    new_environment =
      substract Environment.empty runtime.environment runtime'.environment;
    new_memory =
      runtime'.memory
  }

(** This function displays a difference between two runtimes. *)
let print_observable (_ : runtime) observation =
  Environment.print observation.new_memory observation.new_environment
