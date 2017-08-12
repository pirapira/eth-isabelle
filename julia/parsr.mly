%token LBRACE RBRACE LPAREN RPAREN
%token FUNCTION LET SWITCH DEFAULT CASE FOR BREAK CONTINUE
%token ASSIGN COMMA COLON ARROW 
%token BOOL S8 U8 S32 U32 S64 U64 S128 U128 S256 U256 FALSE TRUE

%token <Z.t> IDENT
%token <Z.t> STRING
%token <Z.t> NUMBER

%token EOS

%{
  open Julia
%}


%start <Julia.statement list> main

%%

main: lst = statement* EOS { lst }

statement:
  st = block { st }
| FUNCTION; id = IDENT; LPAREN; params = typedidentlist?; RPAREN;
  rets = option (ARROW r=typedidentlist {r});
  st = block { FunctionDefinition (id, (match params with None -> [] | Some lst -> lst), (match rets with None -> [] | Some lst -> lst), st)  }
| LET lst = typedidentlist ;
  init = option (ASSIGN e=expression {e}) {
    match init with
    | None -> EmptyVariableDeclaration lst
    | Some expr -> VariableDeclaration (lst, expr)
    }
| lst = identlist ASSIGN e = expression { Assignment (lst, e) }
| e = expression { Expression e }
| SWITCH e = expression cases = case* def = option(DEFAULT b=block {b}) {Switch (e, cases, def) }
| BREAK { Break }
| CONTINUE { Continue }
| FOR LBRACE init=statement* RBRACE cond=expression post=block body=block { ForLoopInit (init, cond, post, body) }

case:
  CASE l=literal b=block { (fst l, snd l, b) }

literal:
  v = literalval COLON t = typename { (v, t) }

literalval:
  FALSE { FalseLiteral }
| TRUE { TrueLiteral }
| l = STRING { StringLiteral l }
| l = NUMBER { NumberLiteral l }

typedidentlist:
  id1 = IDENT COLON t1 = typename;
  lst = list(COMMA idi = IDENT COLON ti = typename { (idi, ti) }) { (id1, t1) :: lst }

identlist:
  id1 = IDENT;
  lst = list(COMMA idi = IDENT { idi }) { id1 :: lst }

typename:
  id = IDENT { CustomType id }
| BOOL { Boolean }
| S8 {S8}
| U8 {U8}
| S32 {S32}
| U32 {U32}
| S64 {S64}
| U64 {U64}
| S128 {S128}
| U128 {U128}
| S256 {S256}
| U256 {U256}

block:
  LBRACE st = statement* RBRACE { Block st }

expression:
| l = literal { Literal (fst l, snd l) }
| id = IDENT LPAREN es = separated_list(COMMA, expression) RPAREN { FunctionCall (id, es) }
| id = IDENT { Identifier id }


