#!/bin/bash
set -x

for file in $1/*; do
#  sed 's/--clausifier[[:space:]].*/--clausifier res\/vclausify_rel/g' $file > $file.tmp
#  sed 's/--clausifier_options.*/--clausifier_options --mode tclausify --ignore_unrecognized_logic on --show_fool true --input_syntax smtlib2 -t 200/g' $file > $file.tmp
#   sed 's/--show_fool true//g'  $file > $file.tmp
 sed 's/--mode tclausify/--mode clausify/g'  $file > $file.tmp 
 mv $file.tmp $file
done

