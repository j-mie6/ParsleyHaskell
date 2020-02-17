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

%define api.pure full

%start nandlang
%%

nandlang : BIT