
%{
#include "Nandlang.tab.h"
#include "stdio.h"
void set_input_string(const char* in);
void end_lexical_scan(void);
%}

%option noyywrap

DIGIT [0-9]
IDLETTER [a-z0-9_A-Z]

%%
[ \t\n]+              ;
\/\/.*\n              ;
(0|1)                 return BIT;
{DIGIT}+              return NAT;
function[^{IDLETTER}] return FUNCTION;
if[^{IDLETTER}]       return IF;
while[^{IDLETTER}]    return WHILE;
var[^{IDLETTER}]      return VAR;
else[^{IDLETTER}]     return ELSE;
[a-z_]{IDLETTER}*     return IDENTIFIER;
\(                    return '(';
\)                    return ')';
\{                    return '{';
\}                    return '}';
\[                    return '[';
\]                    return ']';
;                     return ';';
:                     return ':';
,                     return ',';
!                     return '!';
=                     return '=';
'(\\[0tnvfr]|.)'      return CHAR;
%%

void set_input_string(const char* in) {
  yy_scan_string(in);
}

void end_lexical_scan(void) {
  yy_delete_buffer(YY_CURRENT_BUFFER);
}
