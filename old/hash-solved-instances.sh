#!/bin/sh

cd "$(dirname "$0")"

hash="$(for out in benchmarks/*/*/stdout benchmarks/*/*/*/stdout
  do
    echo "$out"
  done | sort | xargs stat -c '%Y'  | md5sum)"

file=benchmarks/.set-of-solved-instances

if [ -f "$file" ]; then
  test "$(cat "$file")" = "$hash" && exit 0
fi

echo "$hash" > "$file"
