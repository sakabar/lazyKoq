%{
open Lazykoq;;
%}

// リテラル
// なし

// 演算子
// なし

// 括弧類
%token LPAREN   // '('
%token RPAREN   // ')'

// 区切り記号
// なし

// キーワード
%token S
%token K
%token I

// 制御記号
%token EOF 

%start program
%type <Lz.expr> program

%%
program:
  | ccexpr EOF { $1 }
;

ccexpr:
  | ccexpr expr { Lz.A ($1, $2) }
  | expr { $1 }
;

expr:
  | I { Lz.i }
  | K { Lz.k }
  | S { Lz.s }
  | LPAREN ccexpr RPAREN { $2 }

