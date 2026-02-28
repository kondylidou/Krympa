#!/bin/bash
set -x

for file in $1/*; do
  echo "" >> $file
  echo -n $2 >> $file
done

