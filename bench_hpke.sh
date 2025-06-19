#!/bin/bash

set -euxo pipefail

docker run -it --rm -v $(pwd):/root/owlc/ owlc-aeval python3 bench_hpke.py

