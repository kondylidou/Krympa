#!/bin/bash
set -x

for file in $1/*; do
#  sed 's/--clausifier[[:space:]].*/--clausifier res\/vclausify_rel/g' $file > $file.tmp
  sed '/--sub_typing.*/d' $file > $file.tmp
  echo "--sub_typing false" >> $file.tmp 
  mv  $file.tmp $file
#  mv $file.tmp $file
done

