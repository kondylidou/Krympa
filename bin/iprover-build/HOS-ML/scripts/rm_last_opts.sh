#!/bin/bash
set -x

for file in $1/*; do
  head -n -$2 $file > $file.tmp
  mv $file.tmp $file
done

