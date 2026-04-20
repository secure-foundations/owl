#!/bin/bash

# This script sets up the following network configuration:
# - A network namespace `net1`
# - A virtual ethernet interface pair `veth1` and `veth1n`, with `veth1` in the default namespace and
#   `veth1n` residing in the `net1` namespace.
# - `veth1` gets IP address `10.100.1.1`, `veth1n` gets IP address `10.100.1.2`.
# - A Wireguard interface `wg1` in the default namespace, configured according to `wg1.conf`.
# - A Wireguard interface `wg1n` in the `net1` namespace, configured according to `wg1n.conf`.
# The files `wg1.conf` and `wg1n.conf` are expected to be in the same directory as this script.
# The keys therein were generated using `wg genkey` and `wg pubkey`, and their routing tables must
# match the IP addresses assigned within this script.


set -euo pipefail

function usage() {
    echo "Usage: ${0} [-o] [-s] <path-to-wireguard-binary>"
    echo "-o will use the owl option to wireguard-rs (don't use with boringtun)"
    echo "-s SUFFIX" will suffix the output directory with SUFFIX
    echo "-b will pass the --disable-drop-privileges flag to boringtun (only for boringtun)"
    exit 2
}

wireguard_bin=""
use_owl_routines="false"
use_boringtun_args="false"
fd_suffix=""

cur_time=$(date +%Y%m%d%H%M%S)

# Parse command line options
while getopts "s:ob" opt; do
    case "${opt}" in
        o) use_owl_routines="true" ;;
        b) use_boringtun_args="true" ;;
        s) fd_suffix="${OPTARG}" ;;
        \? ) usage ;;
        : ) usage ;;
    esac
done
shift $((OPTIND -1))

# Check if there's a required argument provided
if [[ -n $1 ]]; then
    wireguard_bin=$(realpath "$1")
else
    echo "Path to wireguard-rs is missing" 1>&2
    exit 1
fi

##############################################################
# Set up output log directory

output_dir="iperf-tests/$cur_time-$fd_suffix"
echo "Output directory: $output_dir"
mkdir -p $output_dir

for mss in 100 200 300 400 500 600 700 800 900 1000 1100 1200 1300 1400 1440
do

##############################################################
# Set up network configuration

if [ $use_owl_routines = "true" ]; then
    ./setup-netconfig.sh -o $wireguard_bin
else 
    ./setup-netconfig.sh $wireguard_bin  
fi

##############################################################
# Run test

sleep 5

echo "Running iperf test with MSS $mss"
logfile="$output_dir/iperf_$mss.json"

# Start iperf server in net1 namespace
ip netns exec net1 iperf3 -sD -1 

# Run iperf client in default namespace
iperf3 -c 10.100.2.2 --zerocopy --time 60 --set-mss $mss --logfile $logfile --json



##############################################################
# Clean up network configuration

./cleanup-netconfig.sh

done

