#!/bin/bash

set -euo pipefail

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <arg>"
    exit 1
fi

X="$1"

docker run -it --rm -v $(pwd):/root/owlc/ owlc-aeval cabal run owl -- --extract "$X" 
docker run -it --rm -v $(pwd):/root/owlc/ owlc-aeval ./extraction/run_verus.sh $PWD/extraction

