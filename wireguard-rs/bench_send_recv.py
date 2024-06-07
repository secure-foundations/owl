#!/usr/bin/env python3

import json
import subprocess
from prettytable import PrettyTable
import time

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
        # print(f"Running shell command: {command}")
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
    return (data[NO_OWL]['no_setup'], data[OWL]['no_setup'])
    # print("")
    # print(f"{data[NO_OWL]['no_setup']}")
    # print(f"{data[OWL]['no_setup']}")


def run_bench(base_args):
    command = mk_command(base_args)
    parsed_output = run_cargo_bench_command(command)
    if parsed_output:
        # print(parsed_output)
        data = process_cargo_bench_output(parsed_output)
        
        (no_owl, owl) = prettyData(data)
        return (no_owl, owl)

def run_benches():
    print("Benchmarks with unverified crypto:")
    (unverif_no_owl, unverif_owl) = run_bench(UNVERIF_CRYPTO_ARGS)
    print("")
    print("")
    print("Benchmarks with verified crypto:")
    (verif_no_owl, verif_owl) = run_bench("")
    print("")
    return (unverif_no_owl, unverif_owl, verif_no_owl, verif_owl)

def get_file_contents(filepath):
    with open(filepath, "r") as file:
        return file.read()

def packet_size_test():
    filepath = "./src/wireguard/router/tests/tests.rs"
    saved_file_contents = get_file_contents(filepath)
    # print(saved_file_contents)

    packet_sizes = [0, 1] + list(range(50, 1440, 50)) + [1440]
    print(packet_sizes)
    results = {}
    for packet_size in packet_sizes:
        rust_const_decl = f"const BYTES_PER_PACKET: usize = {packet_size};"
        # print(rust_const_decl)
        print(f"Running test with packet size = {packet_size}")

        # write the packet size to the right file in wireguard-rs source
        with open(filepath, "a") as file:
            file.write(rust_const_decl)
        
        (unverif_no_owl, unverif_owl, verif_no_owl, verif_owl) = run_benches()
        results[packet_size] = {
            'unverif_no_owl': unverif_no_owl, 
            'unverif_owl': unverif_owl,
            'verif_no_owl': verif_no_owl,
            'verif_owl': verif_owl
        }

        # write the original contents back to the file
        with open(filepath, "w") as file:
            file.write(saved_file_contents)
        print("")
        print("")


    table = PrettyTable()
    table.field_names = ["packet size", "unverif crypto baseline ns/iter", "unverif crypto owl ns/iter", "verif crypto baseline ns/iter", "verif crypto owl ns/iter"]
    for packet_size, values in results.items():
        table.add_row([
            packet_size,
            f"{values['unverif_no_owl']:,}", 
            f"{values['unverif_owl']:,}", 
            f"{values['verif_no_owl']:,}",
            f"{values['verif_owl']:,}",
        ])

    print("")
    print("")
    print("Overall packet size microbench results:")
    print(table)
    print("")
    print("Overall packet size microbench results as CSV:")
    print(table.get_formatted_string(out_format="csv"))



if __name__ == "__main__":
    packet_size_test()
    #run_benches()
