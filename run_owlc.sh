#!/bin/bash

set -euo pipefail

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <arg>"
    exit 1
fi

X="$1"

cabal run owl -- --extract "$X" && ./extraction/run_verus.sh $PWD/extraction