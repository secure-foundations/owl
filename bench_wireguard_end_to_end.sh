#!/bin/bash

set -euxo pipefail

python3 bench_wg_linedelay.py --bench_choice go
python3 bench_wg_linedelay.py --bench_choice rs
python3 bench_wg_mss.py --bench_choice go
python3 bench_wg_mss.py --bench_choice rs

