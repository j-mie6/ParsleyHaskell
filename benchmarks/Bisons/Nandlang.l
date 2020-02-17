
%{
#include <stdio.h>
#include "y.tab.h"

void comment();
%}

%%
"//" { comment(); }

