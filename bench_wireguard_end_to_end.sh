#!/bin/bash

set -euxo pipefail

python3 bench_wg_linedelay.py --bench-choice go
python3 bench_wg_linedelay.py --bench-choice rs
python3 bench_wg_mss.py --bench-choice go
python3 bench_wg_mss.py --bench-choice rs

