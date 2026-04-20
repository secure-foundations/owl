#!/usr/bin/env python3


 
# This script sets up the following network configuration:
# - A network namespace `net1`
# - A virtual ethernet interface pair `veth1` and `veth1n`, with `veth1` in the default namespace and
#   `veth1n` residing in the `net1` namespace.
# - `veth1` gets IP address `10.100.1.1`, `veth1n` gets IP address `10.100.1.2`.
# - A Wireguard interface `wg1` in the default namespace, with private key `WG1_PRIVKEY` and 
#   public key `WG1_PUBKEY`, at IP address `10.100.2.1`, listening on port 9101.
# - A Wireguard interface `wg1n` in the `net1` namespace, with private key `WG1N_PRIVKEY` and 
#   public key `WG1N_PUBKEY`, at IP address `10.100.2.2`, listening on port 9102.


import sys
import json
import subprocess
from prettytable import PrettyTable
import argparse

#### CONFIGURATION ####

# This must be kept in sync with setup-netconfig.sh, wg1.conf, wg1n.conf
WG1N_IP_ADDR = "10.100.2.2"
IPERF_CLIENT_OPTS = ""

CARGO_INSTALL_COMMAND = "cargo install --path ."

# Set up and clean up network commands
SUDO = "sudo"
SETUP_SCRIPT = "./setup-netconfig.sh"
CLEANUP_SCRIPT = "./cleanup-netconfig.sh"
USE_OWL_OPT = "--owl"
WIREGUARD_RS_PATH = "$(which wireguard-rs)"
NET1_EXEC = f"{SUDO} ip netns exec net1"

SETUP_OWL_COMMAND = " ".join([SUDO, SETUP_SCRIPT, USE_OWL_OPT, WIREGUARD_RS_PATH])
SETUP_NO_OWL_COMMAND = " ".join([SUDO, SETUP_SCRIPT, WIREGUARD_RS_PATH])
CLEANUP_COMMAND = " ".join([SUDO, CLEANUP_SCRIPT])

# iperf3 commands
IPERF3 = "iperf3"
# run server in one-off daemon mode, so we don't have to worry about killing it
IPERF3_SERVER = f"{IPERF3} -sD -1"
IPERF3_CLIENT = f"{IPERF3} -c {WG1N_IP_ADDR} {IPERF_CLIENT_OPTS}"

def run_command(command, in_net1=False):
    try:
        if in_net1:
            command = f"{NET1_EXEC} {command}"
        print(f"Running shell command: {command}",flush=True)
        # Run the shell command and capture the output
        output = subprocess.check_output(command, shell=True, executable='/bin/bash')
        return output
    except subprocess.CalledProcessError as e:
        print(f"Error executing shell command: {e}")
        sys.exit(1)


def setup_iperf_cleanup(use_owl, wg_path):
    setup_command = SETUP_OWL_COMMAND if use_owl else SETUP_NO_OWL_COMMAND

    # set up the network with wireguard-rs
    setup_network(use_owl, wg_path)

    # # run the iperf3 server in the net1 namespace
    # run_command(IPERF3_SERVER, in_net1=True)

    # # run the iperf3 client in the default namespace and collect output
    # iperf_output = run_command(IPERF3_CLIENT)

    # # cleanup
    run_command(CLEANUP_COMMAND)

    # return iperf_output


def setup_network(use_owl, wg_path):
    owl_opt = USE_OWL_OPT if use_owl else ""
    commands = [
        "sudo ip netns add net1",
        "sudo ip link add veth1 type veth peer veth1n",
        "sudo ip link set veth1n netns net1",
        "sudo ip netns exec net1 ip link set dev lo up",
        "sudo ip link set dev veth1 up",
        "sudo ip netns exec net1 ip link set dev veth1n up",
        "sudo ip addr add 10.100.1.1/24 dev veth1",
        "sudo ip netns exec net1 ip addr add 10.100.1.2/24 dev veth1n",
        "sudo ip netns exec net1 route add default gw 10.100.1.1",
        f"sudo {wg_path} {owl_opt} wg1",
        f"sudo ip netns exec net1 {wg_path} {owl_opt} wg1n"
        "sudo ip addr add 10.100.2.1/24 dev wg1",
        "sudo ip netns exec net1 ip addr add 10.100.2.2/24 dev wg1n"
        "sudo wg setconf wg1 wg1.conf",
        "sudo ip netns exec net1 wg setconf wg1n wg1n.conf",
        "sudo ip link set wg1 up",
        "sudo ip netns exec net1 ip link set wg1n up"
    ]
    for command in commands:
        run_command(command)



def run_bench():
    parser = argparse.ArgumentParser(description='Run WireGuard end-to-end benchmark')
    parser.add_argument('--use-owl', '-o', action='store_true', help='Use owl routines')
    parser.add_argument('wg_path', help='Path to wireguard-rs binary')
    args = parser.parse_args()

    # # make sure wireguard-rs is compiled and installed
    # run_command(CARGO_INSTALL_COMMAND)

    setup_iperf_cleanup(use_owl=args.use_owl, wg_path=args.wg_path)

    # # Baseline (no owl routines)
    # baseline_iperf_output = setup_iperf_cleanup(use_owl=False)

    # # With owl routines
    # owl_iperf_output = setup_iperf_cleanup(use_owl=True)

    # print("Baseline output:")
    # print(baseline_iperf_output)
    # print("Owl output:")
    # print(owl_iperf_output)


if __name__ == "__main__":
    run_bench()




# def process_cargo_bench_output(obj_list):
#     bench_raw = [d for d in obj_list if d['type'] == 'bench']
#     for obj in bench_raw:
#         del obj['type']

#     structured = {}
#     for (name, bench_name) in [(BASELINE, BASELINE_PAT), (NO_OWL, NO_OWL_PAT), (OWL, OWL_PAT)]:
#         objs = [obj for obj in bench_raw if bench_name in obj['name']]
#         assert(len(objs) == 1)
#         structured[name] = {'median': objs[0]['median'], 'deviation': objs[0]['deviation']}

#     return structured

# def prettyData(data):
#     for bench in data.keys():
#         data[bench]['no_setup'] = "N/A"
#         data[bench]['slowdown'] = "N/A"

#     for bench in [NO_OWL, OWL]:
#         data[bench]['no_setup'] = data[bench]['median'] - data[BASELINE]['median']

#     data[OWL]['slowdown'] = (data[OWL]['no_setup']/data[NO_OWL]['no_setup']) - 1

#     # print data as a table
#     table = PrettyTable()
#     table.field_names = ["Benchmark", "ns/iter", "± ns/iter", "without setup", "relative slowdown"]
#     for name, values in data.items():
#         table.add_row([
#             name,
#             f"{values['median']:,}", 
#             f"{values['deviation']:,}", 
#             f"{values['no_setup']:,}" if values['no_setup'] != "N/A" else values['no_setup'], 
#             f"{values['slowdown']:.3%}" if values['slowdown'] != "N/A" else values['slowdown']
#         ])
    
#     print(table)