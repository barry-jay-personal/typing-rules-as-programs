#!/bin/sh
# Build the development with Rocq 9.3.  Extra arguments are passed to make,
# e.g. ./build.sh clean, ./build.sh TIMED=1.
set -eu
cd "$(dirname "$0")"
rocq makefile -f _CoqProject -o Makefile
exec make -f Makefile "$@"
