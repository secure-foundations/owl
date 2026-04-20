#!/bin/bash

set -euo pipefail

function usage() {
    echo "Usage: ${0} [-l|-m] <path-to-json-dir>"
    exit 2
}

json_dir=""
linedelay="false"
mss="false"

# Parse command line options
while getopts "lm" opt; do
    case "${opt}" in
        l) linedelay="true" ;;
        m) mss="true" ;;
        \? ) usage ;;
        : ) usage ;;
    esac
done
shift $((OPTIND -1))

# Check if there's a required argument provided
if [[ -n $1 ]]; then
    json_dir=$(realpath "$1")
else
    echo "Path to json dir is missing" 1>&2
    exit 1
fi

if [ $linedelay = "true" ]; then
    for f in 0ms 0.5ms 1ms 1.5ms 2ms 3ms 4ms 5ms 6ms 7ms 8ms 9ms 10ms
    do
        fname="iperf_$f.json"
        jq '.end.sum_received.bits_per_second' --arg f $f $json_dir/$fname
    done
fi

if [ $mss = "true" ]; then
    for f in 100 200 300 400 500 600 700 800 900 1000 1100 1200 1300 1400 1440
    do
        fname="iperf_$f.json"
        jq '.end.sum_received.bits_per_second' --arg f $f $json_dir/$fname
    done
fi

