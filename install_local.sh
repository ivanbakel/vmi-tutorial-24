#!/bin/bash
opam switch create -y --repositories=default,coq-released=https://coq.inria.fr/opam/released . ocaml-base-compiler.4.14.2-flambda --deps-only
