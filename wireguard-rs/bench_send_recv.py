#!/usr/bin/env python3

import json
import subprocess
from prettytable import PrettyTable

#### CONFIGURATION ####
BASELINE = "bench_send_recv_baseline"
NO_OWL = "bench_send_recv_no_owl"
OWL = "bench_send_recv_owl"

## We need `-Z unstable-options` to get json output. `cargo bench` already requires nightly compiler
BASE_COMMAND = "cargo bench"
BENCH_PATTERN = "bench_send_recv"
BENCH_ARGS = "--format=json -Z unstable-options"
HIDE_STDERR = "2> /dev/null"

COMMAND = " ".join([BASE_COMMAND, "--", BENCH_PATTERN, BENCH_ARGS, HIDE_STDERR])

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
    for (name, bench_name) in [("baseline", BASELINE), ("no_owl", NO_OWL), ("owl", OWL)]:
        objs = [obj for obj in bench_raw if bench_name in obj['name']]
        assert(len(objs) == 1)
        structured[name] = {'median': objs[0]['median'], 'deviation': objs[0]['deviation']}

    return structured

def prettyData(data):
    for bench in data.keys():
        data[bench]['no_baseline'] = "N/A"
        data[bench]['slowdown'] = "N/A"

    for bench in ["no_owl", "owl"]:
        data[bench]['no_baseline'] = data[bench]['median'] - data['baseline']['median']

    data['owl']['slowdown'] = (data['owl']['no_baseline']/data['no_owl']['no_baseline']) - 1

    # print data as a table
    table = PrettyTable()
    table.field_names = ["Benchmark", "ns/iter", "± ns/iter", "without baseline", "relative slowdown"]
    for name, values in data.items():
        table.add_row([
            name, 
            f"{values['median']:,}", 
            f"{values['deviation']:,}", 
            f"{values['no_baseline']:,}" if values['no_baseline'] != "N/A" else values['no_baseline'], 
            f"{values['slowdown']:.3%}" if values['slowdown'] != "N/A" else values['slowdown']
        ])
    
    print(table)


def run_bench():
    parsed_output = run_cargo_bench_command(COMMAND)
    if parsed_output:
        # print(parsed_output)
        data = process_cargo_bench_output(parsed_output)
        
        prettyData(data)

if __name__ == "__main__":
    run_bench()
