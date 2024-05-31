#!/usr/bin/env python3

import json
import subprocess
from prettytable import PrettyTable

#### CONFIGURATION ####
BASELINE = "setup"
BASELINE_PAT = "bench_send_recv_baseline"
NO_OWL = "baseline"
NO_OWL_PAT = "bench_send_recv_no_owl"
OWL = "owl"
OWL_PAT = "bench_send_recv_owl"

## We need `-Z unstable-options` to get json output. `cargo bench` already requires nightly compiler
BASE_COMMAND = "cargo bench"
BENCH_PATTERN = "bench_send_recv"
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
    for (name, bench_name) in [(BASELINE, BASELINE_PAT), (NO_OWL, NO_OWL_PAT), (OWL, OWL_PAT)]:
        objs = [obj for obj in bench_raw if bench_name in obj['name']]
        assert(len(objs) == 1)
        structured[name] = {'median': objs[0]['median'], 'deviation': objs[0]['deviation']}

    return structured

def prettyData(data):
    for bench in data.keys():
        data[bench]['no_setup'] = "N/A"
        data[bench]['slowdown'] = "N/A"

    for bench in [NO_OWL, OWL]:
        data[bench]['no_setup'] = data[bench]['median'] - data[BASELINE]['median']

    data[OWL]['slowdown'] = (data[OWL]['no_setup']/data[NO_OWL]['no_setup']) - 1

    # print data as a table
    table = PrettyTable()
    table.field_names = ["Benchmark", "ns/iter", "± ns/iter", "without setup", "relative slowdown"]
    for name, values in data.items():
        table.add_row([
            name,
            f"{values['median']:,}", 
            f"{values['deviation']:,}", 
            f"{values['no_setup']:,}" if values['no_setup'] != "N/A" else values['no_setup'], 
            f"{values['slowdown']:.3%}" if values['slowdown'] != "N/A" else values['slowdown']
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
