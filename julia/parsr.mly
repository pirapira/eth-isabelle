%token LBRACE RBRACE LPAREN RPAREN
%token FUNCTION ARROW LET SWITCH DEFAULT CASE FOR BREAK CONTINUE
%token ASSIGN COMMA COLON
%token BOOL S8 U8 S32 U32 S64 U64 S128 U128 S256 U256 FALSE TRUE

%token <int> IDENT
%token <int> STRING
%token <int> NUMBER

%token EOS

%start <Julia.statement list> main

%%

main: lst = statement* EOS { lst }

statement:
  st = block { st }
| FUNCTION; id = IDENT; LPAREN; params = typedidentlist?; RPAREN;
  rets = option (ARROW r=typedidentlist? {r});
  st = block { FunctionDeclaration (id, (match params with None -> [] | Some lst -> lst), (match rets with None -> [] | Some lst -> lst), st)  }
| LET lst = typedidentlist ;
  init = option (ASSIGN e=expression {e}) {
    match init with
    | None -> EmptyVariableDeclaration lst
    | Some expr -> VariableDeclaration (lst, init)
    }
| lst = typedidentlist ASSIGN e = expression { Assign (lst, e) }
| e = expression { Expression e }
| SWITCH e = expression cases = case* def = option(DEFAULT b=block {b}) {Switch (e, cases, def) }
| BREAK { Break }
| CONTINUE { Continue }
| FOR init=block cond=expression post=block body=block { For (init, cond, post, body) }

case:
  CASE l=literal b=block { (fst l, snd l, b) }

literal:
  FALSE { FalseLiteral }
| TRUE { TrueLiteral }
| l = STRING { StringLiteral l }
| l = NUMBER { NumberLiteral l }

typedidentlist:
  id1 = IDENT COLON t1 = typename;
  lst = list(COMMA idi = IDENT COLON ti = typename { (idi, ti) }) { (id1, t1) :: lst }

typename:
  id = IDENT { CustomType id }
| BOOL {Boolean}
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
  id = IDENT { Identifier id }

