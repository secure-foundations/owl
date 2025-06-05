#!/usr/bin/env python3

import json
import subprocess
from prettytable import PrettyTable

#### CONFIGURATION ####
BASELINE = " rs ->  rs"
BASELINE_PAT = "bench_rust_rust"
OTR = "owl ->  rs"
OTR_PAT = "bench_owl_rust"
RTO = " rs -> owl"
RTO_PAT = "bench_rust_owl"
OTO = "owl -> owl"
OTO_PAT = "bench_owl_owl"

## We need `-Z unstable-options` to get json output. `cargo bench` already requires nightly compiler
BASE_COMMAND = "cargo bench"
BENCH_PATTERN = ""
BENCH_ARGS = "--format=json -Z unstable-options"
HIDE_STDERR = "2> /dev/null"

UNVERIF_CRYPTO_ARGS = "--features=nonverif-crypto"


def mk_command(base_args):
    return " ".join([BASE_COMMAND, base_args, "--", BENCH_PATTERN, BENCH_ARGS, HIDE_STDERR])


def run_cargo_bench_command(command):
    try:
        print(f"Running shell command: {command}")
        # Run the shell command and capture the output
        output = subprocess.check_output(command, shell=True)
        # print(output)

        # Parse each line of the output as JSON
        parsed_output = [json.loads(line) for line in output.splitlines()]

        return parsed_output
    except subprocess.CalledProcessError as e:
        print(f"Error executing shell command: {e}")
        return None

def process_cargo_bench_output(obj_list):
    bench_raw = [d for d in obj_list if d['type'] == 'bench']
    for obj in bench_raw:
        del obj['type']

    structured = {}
    benchpats = [(BASELINE, BASELINE_PAT), (OTR, OTR_PAT), (RTO, RTO_PAT), (OTO, OTO_PAT)]
    for (name, bench_name) in benchpats:
        objs = [obj for obj in bench_raw if bench_name in obj['name']]
        assert(len(objs) == 1)
        obj = objs[0] 
        structured[name] = {
            'median': obj['median'], 
            'deviation': obj['deviation'], 
        }

    return structured

def prettyData(data):
    for bench in data.keys():
        data[bench]['slowdown'] = "N/A"
        data[bench]['runs/sec'] = 1e9 / data[bench]['median']
        data[bench]['runs/sec_dev'] = ((1e9 / (data[bench]['median'] - data[bench]['deviation'])) - (1e9 / (data[bench]['median'] + data[bench]['deviation'])))/2
        data[bench]['slowdown runs/sec'] = "N/A"


    for bench in [OTR, RTO, OTO]:
        data[bench]['slowdown'] = (data[bench]['median']/data[BASELINE]['median']) - 1
        data[bench]['slowdown runs/sec'] = (data[bench]['runs/sec']/data[BASELINE]['runs/sec']) - 1

    # print data as a table
    table = PrettyTable()
    table.field_names = [
        "Benchmark",
        "ns/iter",
        "± ns/iter",
        "relative slowdown",
        "runs/sec",
        "± runs/sec",
        "rel slowdown runs/sec",
    ]

    for name, values in data.items():
        table.add_row([
            name,
            f"{values['median']:,}", 
            f"{values['deviation']:,}", 
            f"{values['slowdown']:.3%}" if values['slowdown'] != "N/A" else values['slowdown'],
            f"{values['runs/sec']:,.1f}" if values['runs/sec'] != "N/A" else values['runs/sec'], 
            f"{values['runs/sec_dev']:,.1f}" if values['runs/sec_dev'] != "N/A" else values['runs/sec_dev'], 
            f"{values['slowdown runs/sec']:.3%}" if values['slowdown runs/sec'] != "N/A" else values['slowdown runs/sec'],
        ])
    
    print(table)


def run_bench(base_args):
    command = mk_command(base_args)
    parsed_output = run_cargo_bench_command(command)
    if parsed_output:
        # print(parsed_output)
        data = process_cargo_bench_output(parsed_output)
        
        prettyData(data)

def run_benches():
    print("Benchmarks with unverified crypto:")
    run_bench(UNVERIF_CRYPTO_ARGS)
    print("")    
    print("")
    print("Benchmarks with verified crypto:")
    run_bench("")
    print("")


if __name__ == "__main__":
    run_benches()
