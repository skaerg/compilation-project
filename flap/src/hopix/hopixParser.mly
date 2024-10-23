%{ (* -*- tuareg -*- *)

  open HopixAST
  open Position


%}

%token EOF

%token AND DO ELSE EXTERN FOR FROM FUN IF LET MATCH REF THEN TO TYPE UNTIL WHILE

%token ARROW

%token<string> TYPE_VARIABLE CONSTR_ID LOWERCASE_ID

%token<Mint.t> INT
%token<char> CHAR
%token<string> STRING

%token EQUAL LANGLE RANGLE LPAREN RPAREN LCURLY RCURLY LSQUARE RSQUARE BAR AMPERSAND ASSIGN COLON SEMICOLON COMMA EMARK PLUS MINUS STAR SLASH BACKSLASH UNDERSCORE DOT LOGICAL_AND LOGICAL_OR EQUAL_TEST LESS_OR_EQ_TEST GREATER_OR_EQ_TEST LESS_TEST GREATER_TEST

%nonassoc LOW
%right SEMICOLON
%nonassoc INT CHAR STRING
%nonassoc LOWERCASE_ID CONSTR_ID
%nonassoc IF MATCH FOR WHILE DO
%nonassoc LET FUN REF
%right ASSIGN
%right ARROW
%right LOGICAL_OR
%right LOGICAL_AND
%left EQUAL EQUAL_TEST LESS_OR_EQ_TEST GREATER_OR_EQ_TEST LESS_TEST GREATER_TEST BAR AMPERSAND
%left PLUS MINUS
%nonassoc PLUS_MINUS
%left STAR SLASH
%nonassoc STAR_SLASH
%nonassoc COLON
%left DOT
%nonassoc LPAREN LCURLY
%left EMARK
%nonassoc BACKSLASH
%nonassoc HIGH

%start<HopixAST.t> program

%%


(* Program *)

program: definition_list=list(located(definition)) EOF
{
  definition_list
}

definition: TYPE type_cons=located(type_constructor) 
type_var_list=loption(delimited(LANGLE, type_variables, RANGLE)) 
type_def=option(preceded(EQUAL, type_definition))
{
  match type_def with
    | None   -> DefineType(type_cons, type_var_list, Abstract)
    | Some t -> DefineType(type_cons, type_var_list, t)
}
| EXTERN vi=located(identifier) COLON ts=located(type_scheme) { DeclareExtern (vi, ts) }
| vd=value_definition { DefineValue(vd) }
| error 
{ Error.error "parsing" (Position.lex_join $startpos $endpos) "Syntax error." }

type_variables: tvars=separated_nonempty_list(COMMA, located(type_variable)) { tvars }

type_definition: option(BAR) 
type_def_elements=separated_nonempty_list(BAR, type_def_element)
{
  DefineSumType type_def_elements
}
| ls=delimited(
  LCURLY, 
  separated_nonempty_list(COMMA, separated_pair(located(label), COLON, located(ty))), 
  RCURLY)
{
  DefineRecordType ls
}

type_def_element: cons=located(constructor) ty_list=loption(delimited(LPAREN, separated_nonempty_list(COMMA, located(ty)), RPAREN))
{ (cons, ty_list) }

value_definition : 
  LET vi=located(identifier) ts=option(preceded(COLON, located(type_scheme))) EQUAL e=located(expression)
  { SimpleValue (vi, ts, e) }
| FUN fd=separated_nonempty_list(AND, function_definition)
  { RecFunctions fd}

function_definition : vi=located(identifier) ts=option(preceded(COLON, located(type_scheme))) p=located(pattern) EQUAL e=located(expression) 
{ (vi, ts, FunctionDefinition (p, e)) } 



(* Datatypes *)

ty:
  tc=type_constructor
  ty_list=loption(delimited(
    LANGLE,
    separated_nonempty_list(COMMA, located(ty)),
    RANGLE))
{ 
  TyCon (tc, ty_list)
}
| type_l=located(ty) ARROW type_r=located(ty)
  {
    TyArrow (type_l, type_r)
  }
| t1=located(ty) STAR t2=located(ty)
  {
    TyTuple(t1::[t2])
  }
| tvar=type_variable { TyVar tvar }
| t=delimited(LPAREN, ty, RPAREN) { t }

type_scheme : 
type_var_list=loption(delimited(LSQUARE, type_variables, RSQUARE)) t=located(ty)
{ 
  ForallTy (type_var_list, t)
}

optional_type_list:
  ptl=option(delimited(LANGLE, separated_list(COMMA, located(ty)), RANGLE))
  {
    ptl
  }

(* Expressions *)

expression : 
  lit=located(literal) { Literal(lit) }
| vid=located(identifier) tyl=optional_type_list
{ Variable (vid,tyl) }
| kid=located(constructor) 
  tyl=optional_type_list
{
  Tagged (kid, tyl, [])
} %prec LOW
| kid=located(constructor) 
  tyl=optional_type_list
  expl=expression_list
{
  Tagged (kid, tyl, expl)
}
| LPAREN
  e_first=located(expression) COMMA
  e_rest=separated_nonempty_list(COMMA, located(expression))
  RPAREN
{
  Tuple(e_first::e_rest)
}
| LPAREN e=expression RPAREN
  { e }
| LCURLY
  ls=separated_nonempty_list(
    COMMA, separated_pair(located(label), EQUAL, located(expression)))
  RCURLY
  ty_list=optional_type_list
{ Record (ls,ty_list) }
| e=located(expression) DOT l=located(label) tyl=optional_type_list
  { Field (e, l, tyl) }
| e1=located(expression) SEMICOLON e2=located(expression)
  { Sequence (e1::[e2]) } %prec LOW
| vd=value_definition SEMICOLON e=located(expression)
  { Define (vd, e) }
| BACKSLASH p=located(pattern) ARROW e=located(expression)
  { Fun(FunctionDefinition(p, e)) } %prec LOW
| e1=located(expression) e2=located(expression)
  {
    Apply (e1, e2)
  } %prec HIGH
  (* see https://ptival.github.io/2017/05/16/parser-generators-and-function-application/ *)
| e1=located(expression) o=plus_minus e2=located(expression)
  {
    let o_id = Position.with_poss $startpos $endpos (Id(o))
    in let o_var = Position.with_poss $startpos $endpos (Variable(o_id, None))
    in let apply_o_e1 = Position.with_poss $startpos $endpos (Apply(o_var, e1))
    in Apply(apply_o_e1, e2)
  } %prec PLUS_MINUS
| e1=located(expression) o=star_slash e2=located(expression)
  {
    let o_id = Position.with_poss $startpos $endpos (Id(o))
    in let o_var = Position.with_poss $startpos $endpos (Variable(o_id, None))
    in let apply_o_e1 = Position.with_poss $startpos $endpos (Apply(o_var, e1))
    in Apply(apply_o_e1, e2)
  } %prec STAR_SLASH
| e1=located(expression) o=other_binop e2=located(expression)
  {
    let o_id = Position.with_poss $startpos $endpos (Id(o))
    in let o_var = Position.with_poss $startpos $endpos (Variable(o_id, None))
    in let apply_o_e1 = Position.with_poss $startpos $endpos (Apply(o_var, e1))
    in Apply(apply_o_e1, e2)
  } %prec LOW
| MATCH e=delimited(LPAREN,located(expression), RPAREN) 
  l=delimited(LCURLY, branches, RCURLY) 
{ Case (e,l) }
| IF e1=delimited(LPAREN, located(expression), RPAREN)
  THEN e2=delimited(LCURLY, located(expression), RCURLY)
  e3=option(preceded(ELSE, delimited(LCURLY, located(expression), RCURLY)))
{ 
  match e3 with
    | None   -> IfThenElse (e1,e2,(Position.unknown_pos (Tuple([]))))
    | Some b -> IfThenElse (e1,e2,b)
}
| REF e=located(expression) { Ref (e) } %prec HIGH
| e1=located(expression) ASSIGN e2=located(expression)
  { Assign(e1, e2) }
| EMARK e=located(expression) { Read (e) }
| WHILE LPAREN e1=located(expression) RPAREN LCURLY e2=located(expression) RCURLY
{ While (e1, e2) }
| DO LCURLY e1=located(expression) RCURLY UNTIL LPAREN e2=located(expression) RPAREN
  {
    let w = While (e2, e1)
    in let located_w = (Position.with_poss $startpos $endpos w)
    in Sequence(e1::[located_w])
  }
| FOR vid=located(identifier) FROM
  e1=delimited(LPAREN, located(expression), RPAREN) TO
  e2=delimited(LPAREN, located(expression), RPAREN)
  e3=delimited(LCURLY, located(expression), RCURLY)
{ For (vid, e1, e2, e3) }
| LPAREN e=located(expression) COLON t=located(ty) RPAREN
{ TypeAnnotation (e,t) }


(* Auxiliary definitions *)

plus_minus: (* as per hopixPrettyPrinter.ml *)
  PLUS               { "`+`"   }
| MINUS              { "`-`"   }

star_slash:
  STAR               { "`*`"   }
| SLASH              { "`/`"   }

other_binop:
  LOGICAL_AND        { "`&&`"  }
| LOGICAL_OR         { "`||`"  }
| EQUAL_TEST         { "`=?`"  }
| LESS_OR_EQ_TEST    { "`<=?`" }
| GREATER_OR_EQ_TEST { "`>=?`" }
| LESS_TEST          { "`<?`"  }
| GREATER_TEST       { "`>?`"  }

branches : option(BAR) l=separated_nonempty_list(BAR, located(branch))
{ l }

branch : p=located(pattern) ARROW e=located(expression)
{ Branch (p,e) }

expression_list: 
  l=delimited(
    LPAREN,
    separated_nonempty_list(COMMA, located(expression)),
    RPAREN
  )
  {
    l
  }


(* Patterns *)

pattern : 
  vi=located(identifier) { PVariable(vi) }
| UNDERSCORE { PWildcard }
| LPAREN
  p_first=located(pattern) COMMA
  p_rest=separated_nonempty_list(COMMA, located(pattern))
  RPAREN
  { 
    PTuple (p_first::p_rest)
  }
| LPAREN t=pattern RPAREN
  {
    t
  }
| p=located(pattern) COLON t=located(ty) { PTypeAnnotation (p, t)}
| lit=located(literal) { PLiteral (lit) }
| kid=located(constructor)
  ty_list=optional_type_list
  p_list=loption(delimited(LPAREN, separated_list(
    COMMA, located(pattern)), RPAREN))
{ PTaggedValue (kid,ty_list,p_list) }
| LCURLY 
  ls=separated_nonempty_list(
    COMMA, separated_pair(located(label), EQUAL, located(pattern)))
  RCURLY
  ty_list=optional_type_list
{ PRecord(ls,ty_list) }
| p1=located(pattern) BAR p2=located(pattern)
{ POr (p1::[p2]) }
| p1=located(pattern) AMPERSAND p2=located(pattern)
{ PAnd (p1::[p2])}



(* Identifiers *)

identifier : vid=LOWERCASE_ID { Id(vid) }
type_constructor: c=LOWERCASE_ID { TCon(c) }
label : lid=LOWERCASE_ID { LId(lid) }
constructor : k=CONSTR_ID { KId k }
type_variable: v=TYPE_VARIABLE { TId(v) }

literal : i=INT { LInt i }
| s=STRING { LString s }
| c=CHAR { LChar c }


%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
