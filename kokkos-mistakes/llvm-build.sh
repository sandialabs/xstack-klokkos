#!/usr/bin/env bash

KOKKOS_MOCK_DIR=${KOKKOS_MOCK_DIR:-../kokkos-mock}
KLEE_DIR=${KLEE_DIR:-../klee/install}
BITCODE=build-bitcode
examples=(example1 example2 example3 example3-1 example4 example5 example5-1)

function is-binary {
  type "$1" &>/dev/null
}

mkdir -p $BITCODE
for src in ${examples[@]}; do
  clang -g -O0 -c -emit-llvm -I${KOKKOS_MOCK_DIR} -isystem ${KLEE_DIR}/include -DWITH_BUG=1 -o "${BITCODE}/${src}-buggy.bc" "${src}.cpp"
  clang -g -O0 -c -emit-llvm -I${KOKKOS_MOCK_DIR} -isystem ${KLEE_DIR}/include              -o "${BITCODE}/${src}-nobug.bc" "${src}.cpp"
  if is-binary dot; then
    opt -enable-new-pm=0 -analyze -dot-callgraph "${BITCODE}/${src}-buggy.bc" >/dev/null
    cat "${BITCODE}/${src}-buggy.bc.callgraph.dot" | \
      c++filt --no-params --no-verbose | \
      sed 's,>,\\>,g; s,-\\>,->,g; s,<,\\<,g' | \
      gawk '/external node/{id=$1} $1 != id' | \
      dot -Tpdf -ocg-${src}.pdf
    rm -f "${BITCODE}/${src}-buggy.bc.callgraph.dot"
  fi
  llvm-dis -o - "${BITCODE}/${src}-buggy.bc" | c++filt > "${BITCODE}/${src}-buggy.ll"
  llvm-dis -o - "${BITCODE}/${src}-nobug.bc" | c++filt > "${BITCODE}/${src}-nobug.ll"
done
