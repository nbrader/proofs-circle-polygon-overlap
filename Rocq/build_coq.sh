#!/bin/bash

set -e  # Exit on error

# Ensure we use the same opam switch as the IDE (rocq-8.18.0)
eval $(opam env --switch=rocq-8.18.0)

# Choose build method: make (default) or dune
BUILD_METHOD=${1:-make}

if [ "$BUILD_METHOD" = "dune" ]; then
    dune clean 2>&1 | grep -E "(Error|error)" || true
    dune build --display=short
    echo "✓ Build successful (dune)"
elif [ "$BUILD_METHOD" = "make" ]; then
    make clean 2>/dev/null || true
    coq_makefile -f _CoqProject -o Makefile 2>&1 | grep -E "(Error|error)" || true
    make 2>&1 | grep -vE "^(ROCQ|CLEAN)" || true
    echo "✓ Build successful (make)"
else
    echo "Error: Unknown build method '$BUILD_METHOD'"
    echo "Usage: $0 [dune|make]"
    exit 1
fi