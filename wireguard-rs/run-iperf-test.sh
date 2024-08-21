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
# Set up virtual ethernet interface pair

# Set up network namespace
ip netns add net1

# Set up virtual ethernet interface pair
ip link add veth1 type veth peer veth1n

# Move veth1n into the net1 namespace
ip link set veth1n netns net1

# Bring up loopback in the net1 namespace
ip netns exec net1 ip link set dev lo up

# Bring up the network interfaces
ip link set dev veth1 up
ip netns exec net1 ip link set dev veth1n up

# Add IP addresses to veth1 and veth1n
ip addr add 10.100.1.1/24 dev veth1
ip netns exec net1 ip addr add 10.100.1.2/24 dev veth1n

# Add default route to the net1 namespace
ip netns exec net1 route add default gw 10.100.1.1


##############################################################
# Set up wireguard interfaces

# Create Wireguard interfaces, wg1 in default namespace, wg1n in net1 namespace
if [ $use_owl_routines = "true" ]; then
    echo "Using owl routines"
    $wireguard_bin --owl wg1
    ip netns exec net1 $wireguard_bin --owl wg1n
else 
    if [ $use_boringtun_args = "true" ]; then
        echo "Using boringtun with --disable-drop-privileges"
        $wireguard_bin --disable-drop-privileges --disable-multi-queue --threads 1 wg1
        ip netns exec net1 $wireguard_bin --disable-drop-privileges --disable-multi-queue --threads 1 wg1n
    else
        $wireguard_bin wg1
        ip netns exec net1 $wireguard_bin wg1n
    fi
fi

# Add IP addresses to Wireguard interfaces
ip addr add 10.100.2.1/24 dev wg1
ip netns exec net1 ip addr add 10.100.2.2/24 dev wg1n

# Configure the Wireguard interfaces
wg setconf wg1 wg1.conf
ip netns exec net1 wg setconf wg1n wg1n.conf

# Bring up the Wireguard interfaces
ip link set wg1 up
ip netns exec net1 ip link set wg1n up


##############################################################
# Run test

echo "Running iperf test with MSS $mss"
logfile="$output_dir/iperf_$mss.json"

# Start iperf server in net1 namespace
ip netns exec net1 iperf3 -sD -1 

# Run iperf client in default namespace
iperf3 -c 10.100.2.2 --zerocopy --time 60 --set-mss $mss --logfile $logfile --json



##############################################################
# Clean up network configuration

# Delete wg1 interface
ip link del wg1
ip netns exec net1 ip link del wg1n

# Delete veth1 interface
ip link del veth1

# Delete net1 namespace. This deletes veth1n interface too
ip netns del net1

done

