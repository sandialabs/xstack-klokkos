#!/bin/sh
set -u
# You better not have ?s in your pathnames
printf  "Generating makefile..."
coq_makefile -f _CoqProject -o Makefile
printf "Now type make"

