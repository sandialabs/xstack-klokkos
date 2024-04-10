#!/usr/bin/env bash

for src in *.cpp; do
  basename="$(basename -s .cpp $src)"
  clang -g -O0 -c -emit-llvm -I../../DataRaceDetection/kokkos-model -DWITH_BUG=1 $src
  clang -g -O0 -c -emit-llvm -I../../DataRaceDetection/kokkos-model -o "${basename}-nobug.bc" $src
  opt -enable-new-pm=0 -analyze -dot-callgraph "$basename.bc" >/dev/null
  cat "$basename.bc.callgraph.dot" | \
    c++filt --no-params --no-verbose | \
    sed 's,>,\\>,g; s,-\\>,->,g; s,<,\\<,g' | \
    gawk '/external node/{id=$1} $1 != id' | \
    dot -Tpdf -ocg-${basename}.pdf

 llvm-dis -o - "$basename.bc" | c++filt > "$basename.ll"
 llvm-dis -o - "$basename-nobug.bc" | c++filt > "$basename-nobug.ll"
 rm -f "$basename.bc.callgraph.dot"
done
