#!/bin/bash

set -euxo pipefail

docker run -it --rm -v $(pwd):/root/owlc/ owlc-aeval python3 microbench_wg_handshake.py

