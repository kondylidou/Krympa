#!/bin/bash
set -x

for file in $1/*; do
  awk 'NF' $file > $file.tmp
  mv $file.tmp $file
done

