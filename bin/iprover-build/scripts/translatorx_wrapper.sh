#!/bin/bash
#
# rectifies TranslatorX output
#
# 1. remove brecets around variables (X)
# fof(axiom_name_13,axiom,((Y=p9f0(X,Y))=>(Y)=p9f0(i(X),Y))).
# careful with e.g. i(X)
#
# 2.
# cut lines unitl "TPTP"
#
# 
sed -E 's/([^a-z0-9])[(]([A-Z]+)[)]/\1\2/g' | sed -E '1,/TPTP/d' <&0
