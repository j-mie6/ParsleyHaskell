%{
#include <stdbool.h>
bool parse(const char*);
extern int yylex(void);
void yyerror(const char* err);
%}

/* A Parser for Nandlang */
%token IDENTIFIER
%token BIT
%token NAT
%token CHAR
%token FUNCTION
%token IF
%token WHILE
%token VAR
%token ELSE

%start nandlang
%%

nandlang : funcdef nandlang | %empty ;
index : '[' natorbit ']' ;
natorbit : NAT | BIT ;
variable : IDENTIFIER | IDENTIFIER index ;
literal : BIT | CHAR ;
expr : expr '!' nandexpr | nandexpr ;
nandexpr : literal | funccallOrVar ;
funccallOrVar : IDENTIFIER '(' exprlist ')'
              | IDENTIFIER index
              | IDENTIFIER ;
exprlist : exprlist1 | %empty ;
exprlist1 : expr ',' exprlist1
          | expr ;
varlist : varlist1 | %empty ;
varlist1 : variable ',' varlist1
         | variable ;
funcparam : varlist ':' varlist
          | varlist ;
varstmt : VAR varlist1 '=' exprlist1 ';'
        | varlist1 '=' exprlist1 ';' ;
ifstmt : IF expr block elsestmt ;
elsestmt : ELSE block | %empty ;
whilestmt : WHILE expr block ;
statement : ifstmt | whilestmt | varstmt | expr ';' ;
block : '{' statements '}'
statements : statement statements | %empty ;
funcdef : FUNCTION IDENTIFIER '(' funcparam ')' block

%%

void set_input_string(const char* in);
void end_lexical_scan(void);

bool parse(const char* in) 
{
  set_input_string(in);
  int rv = yyparse();
  end_lexical_scan();
  return !rv;
}

void yyerror(const char* msg) 
{
    return;
}