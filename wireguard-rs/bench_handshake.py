#!/usr/bin/env python3

import json
import subprocess
from prettytable import PrettyTable

#### CONFIGURATION ####
BASELINE = " rs ->  rs"
BASELINE_PAT = "bench_h_1_rs_handshake"
BASELINE_INIT_PAT = "bench_h_1_rs_handshake_init"
OTR = "owl ->  rs"
OTR_PAT = "bench_h_2_owl_init_rs_resp_handshake"
OTR_INIT_PAT = "bench_h_2_owl_init_rs_resp_handshake_init"
RTO = " rs -> owl"
RTO_PAT = "bench_h_3_rs_init_owl_resp_handshake"
RTO_INIT_PAT = "bench_h_3_rs_init_owl_resp_handshake_init"
OTO = "owl -> owl"
OTO_PAT = "bench_h_4_owl_handshake"
OTO_INIT_PAT = "bench_h_4_owl_handshake_init"


## We need `-Z unstable-options` to get json output. `cargo bench` already requires nightly compiler
BASE_COMMAND = "cargo bench"
BENCH_PATTERN = "bench_h"
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
    benchpats = [(BASELINE, BASELINE_PAT, BASELINE_INIT_PAT), (OTR, OTR_PAT, OTR_INIT_PAT), (RTO, RTO_PAT, RTO_INIT_PAT), (OTO, OTO_PAT, OTO_INIT_PAT)]
    for (name, bench_name, init_name) in benchpats:
        objs = [obj for obj in bench_raw if bench_name in obj['name']]
        assert(len(objs) == 2)
        init_obj = objs[0] if init_name in objs[0]['name'] else objs[1]
        handshake_obj = objs[1] if init_name in objs[0]['name'] else objs[0]
        structured[name] = {
            'median': handshake_obj['median'], 
            'deviation': handshake_obj['deviation'], 
            'init_median': init_obj['median'], 
            'init_deviation': init_obj['deviation']
        }

    return structured

def prettyData(data):
    for bench in data.keys():
        data[bench]['no_init'] = data[bench]['median'] - data[bench]['init_median']
        data[bench]['slowdown'] = "N/A"
        data[bench]['handshakes/sec'] = 1e9 / data[bench]['no_init']
        data[bench]['slowdown handshakes/sec'] = "N/A"


    for bench in [OTR, RTO, OTO]:
        data[bench]['slowdown'] = (data[bench]['no_init']/data[BASELINE]['no_init']) - 1
        data[bench]['slowdown handshakes/sec'] = abs((data[bench]['handshakes/sec']/data[BASELINE]['handshakes/sec']) - 1)


    # print data as a table
    table = PrettyTable()
    table.field_names = ["Benchmark", "ns/iter", "± ns/iter", "setup ns/iter", "without setup ns/iter", "relative slowdown", "handshakes/sec", "relative slowdown handshakes/sec"]
    for name, values in data.items():
        table.add_row([
            name,
            f"{values['median']:,}", 
            f"{values['deviation']:,}", 
            f"{values['init_median']:,}",
            f"{values['no_init']:,}" if values['no_init'] != "N/A" else values['no_init'], 
            f"{values['slowdown']:.3%}" if values['slowdown'] != "N/A" else values['slowdown'],
            f"{values['handshakes/sec']:,.5}" if values['handshakes/sec'] != "N/A" else values['handshakes/sec'], 
            f"{values['slowdown handshakes/sec']:.3%}" if values['slowdown handshakes/sec'] != "N/A" else values['slowdown handshakes/sec']
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
    print("Benchmarks with verified crypto:")
    run_bench("")
    print("")
    print("")
    print("Benchmarks with unverified crypto:")
    run_bench(UNVERIF_CRYPTO_ARGS)
    print("")


if __name__ == "__main__":
    run_benches()
