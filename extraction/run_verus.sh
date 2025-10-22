#!/bin/bash

set -euo pipefail

function usage() {
    echo "Usage: ${0} [-n] [-v <verus-args>] <path-to-extraction-dir>"
    echo "  -n: Do not format the code"
    echo "  -v <verus-args>: Additional arguments to pass to verus"
    echo "You must have verus and verusfmt in your path"
    exit 2
}

format="true"
ext_dir_path=""
verus_args=""

# Parse command line options
while getopts "v:n" opt; do
    case "${opt}" in
        n) format="false" ;;
        v) verus_args="${OPTARG}" ;;
        \? ) usage ;;
        : ) usage ;;
    esac
done
shift $((OPTIND -1))

# Check if there's a required argument provided
if [[ -n $1 ]]; then
    ext_dir_path=$(realpath "$1")
else
    echo "Path to extraction dir is missing." 1>&2
    exit 1
fi

src_path=$ext_dir_path/src

main_file=$src_path/lib.rs

if [ $format = "true" ]; then
    echo ""
    echo "FORMATTING"
    verusfmt $main_file
fi

echo ""
echo "CARGO VERUS BUILD"
pushd $ext_dir_path
cargo verus verify -- --rlimit=100 --no-lifetime $verus_args
popd

if [ -z $verus_args ]; then
    echo ""
    echo "Done!" 
else
    echo ""
    echo ""
    echo "WARNING: using the following extra verus args: $verus_args"
    echo ""
fi

