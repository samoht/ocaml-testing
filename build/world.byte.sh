#!/bin/sh
set -e
cd `dirname $0`/..
source build/targets.sh
set -x
$OCAMLBUILD $@ \
  $STDLIB_BYTE $OCAMLC_BYTE $OCAMLLEX_BYTE $OCAMLOPT_BYTE $TOPLEVEL $TOOLS_BYTE \
  $OTHERLIBS_BYTE $OCAMLBUILD_BYTE $DEBUGGER $OCAMLDOC_BYTE $CAMLP4_BYTE
