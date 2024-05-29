#!/bin/bash

set -euo pipefail

function usage() {
    echo "Usage: ${0} [-n] <path-to-extraction-dir>"
    echo "You must have verus and verusfmt in your path,"
    echo "and the PARSLEYPATH environment variable set to the path"
    echo "to the crate root of the parsley repo."
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

main_file=$src_path/main.rs
vest_file=$src_path/parse_serialize.vest

if [ $format = "true" ]; then
    echo ""
    echo "FORMATTING"
    verusfmt $main_file
fi

echo ""
echo "VERIFYING, COMPILING, AND EXPORTING PARSLEY" 
pushd $PARSLEYPATH
make
popd

echo ""
echo "COMPILING LIB FILE" 
pushd $ext_dir_path 
cargo build --lib
popd

echo ""
echo "VERIFYING" 
verus -L dependency=$(realpath $ext_dir_path/target/debug/deps) $( find $ext_dir_path/target/debug/deps -name \*.rlib -exec realpath '{}' ';' | awk -F/ '{print "--extern " substr ($NF,4,index($NF,"-") - 4) "=" $0}' | grep -v vstd | grep -v builtin ) --extern parsley=$PARSLEYPATH/libparsley.rlib --import parsley=$PARSLEYPATH/parsley.verusdata --multiple-errors=100 --rlimit=100 $main_file $verus_args -V spinoff-all



if [ -z $verus_args ]; then
    echo ""
    echo "Done!" 
else
    echo ""
    echo ""
    echo "WARNING: using the following extra verus args: $verus_args"
    echo ""
fi

