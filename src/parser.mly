
%{
open Horsz
open Apt
%}

%token <int> INT
%token <string> ID
%token <string> OP
%token <string> PRED
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token LBRACE
%token RBRACE
%token COMMA
%token COLLON
%token SEMICOLLON
%token IF
%token THEN
%token ELSE
%token EQUAL
%token OTYPE
%token INTTYPE
%token ARROW
%token DARROW
%token NOT
%token EOF

%nonassoc ELSE
%right    ARROW 
%left     OP
%nonassoc INT IF ID LPAREN
%left prec_app

%start <(Horsz.program * Apt.apt) option> prog
%%

prog:
  | LPAREN LBRACE; s = statements; RBRACE; COMMA; v = expr; RPAREN; apt = apt EOF 
    { Some (Prog (s, v), apt) }
  ;

statements:
  | s = statement { [s] }
  | s = statement; SEMICOLLON; ss = statements { s :: ss }
  ;

statement:
  | f = ID; args = vars; COLLON; t = ty; EQUAL; e = expr { Statement (f, args, t, e) }  
  | f = ID; COLLON; t = ty; EQUAL; e = expr { Statement (f, [], t, e) }  
  ;

vars:
  | v = ID { [v] }
  | v = ID; vs = vars { v :: vs }
  ;

ty:
  | OTYPE { O }
  | INTTYPE; ARROW; t = ty { Arr (TInt, t) }
  | t1 = ty; ARROW; t2 = ty { Arr (Ty t1, t2) }
  | LPAREN; t = ty; RPAREN { t }


expr:
  | v = ID { Var v }
  | n = INT { Int n }
  | e1 = expr; op = OP; e2 = expr { Op (op, e1, e2) }
  | IF; e1 = expr ; p = PRED; e2 = expr; THEN; e3 = expr; ELSE; e4 = expr 
    { If (Pred (true, p, [e1; e2]), e3, e4) }
  | IF; e1 = expr ; EQUAL; e2 = expr; THEN; e3 = expr; ELSE; e4 = expr 
    { If (Pred (true, "=", [e1; e2]), e3, e4) }
  | IF; EQUAL; LPAREN; es = exprs; RPAREN THEN; e1 = expr; ELSE; e2 = expr 
    { If (Pred (true, "=", es), e1, e2) }
  | IF; p = PRED; LPAREN; es = exprs; RPAREN THEN; e1 = expr; ELSE; e2 = expr
    { If (Pred (true, p, es), e1, e2) }
  | IF NOT ; p = PRED; LPAREN; es = exprs; RPAREN THEN; e1 = expr; ELSE; e2 = expr
    { If (Pred (false, p, es), e1, e2) }
  | a = ID; LBRACKET; es = exprs; RBRACKET
    { Cont (a, es)}
  | e1 = expr; e2 = expr %prec prec_app { App (e1, e2) }
  | LPAREN; e = expr; RPAREN { e }
  ;

exprs:
  | e = expr { [e] }
  | e = expr; COMMA; es = exprs { e :: es }
  ;

states:
  | LBRACE; ids = ids; RBRACE { ids }
  ;

ids: 
  | id = ID { [id] }
  | id = ID; COMMA;  ids = ids { id :: ids }
  ;

alphabet:
  | LBRACE; ii = id2ints; RBRACE { ii }
  ;

id2ints:
  | id = ID; ARROW; i = INT { [id, i] }
  | id = ID; ARROW; i = INT; COMMA; ii = id2ints { (id, i)::ii }
  ;

transs:
  | t = trans { [t] }
  | t = trans; COMMA; ts = transs { t :: ts }
  ;

trans:
  | LPAREN; id1 = ID; COMMA; id2 = ID; RPAREN; DARROW; LBRACE; te = trans_elems2; RBRACE
    { ((id1, id2), te) }
  ;

trans_elems2:
  | LBRACE; RBRACE { [[]] }
  | LBRACE; te = trans_elems; RBRACE { [te] }
  | LBRACE; te = trans_elems; RBRACE; COMMA; te2 = trans_elems2 { te :: te2 }
  ;

trans_elems:
  | LPAREN; i = INT; COMMA; id = ID; RPAREN { [i, id] }
  | LPAREN; i = INT; COMMA; id = ID; RPAREN; COMMA; te = trans_elems 
    { (i, id) :: te }
  ;

apt:
  | LPAREN; states = states; COMMA; alphabet = alphabet; COMMA; initial_state = ID; COMMA; LBRACE; trans = transs; RBRACE; COMMA; priority = alphabet; RPAREN
    { {states; alphabet; initial_state; trans; priority; max_priority=max_priority priority} }
  ;

/* trans:
  | LPAREN; e0 = ID; COMMA; e1 = ID; COMMA; e2 = ID;RPAREN { (e0, e1, e2) }

transes:
  | e = trans { [e] }
  | e = trans; SEMICOLLON; es = transes { e::es } */
