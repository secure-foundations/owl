#!/bin/bash

set -euxo pipefail

docker run -it --rm -v $(pwd):/root/owlc/ owlc-aeval python3 run_owlc_on_all.py

