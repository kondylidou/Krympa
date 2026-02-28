#!/bin/bash
#set -x

for file in $1/*; do
  n=$(grep sub_typing $file | wc -l)
  if [ "$n" -gt "2" ]; then   
    echo "$n"
    echo "$file"
  fi  
done

