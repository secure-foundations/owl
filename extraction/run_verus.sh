#!/bin/bash

set -euo pipefail

function usage() {
    echo "Usage: ${0} [-n|--nofmt] <path-to-extraction-dir>"
    echo "You must have verus and verusfmt in your path,"
    echo "and the VESTPATH environment variable set to the path"
    echo "to the crate root of the vest codegen repo."
    exit 2
}

format="true"
ext_dir_path=""

# Parse command line options
while getopts "nofmt,n," opt; do
    case ${opt} in
        n | nofmt ) format="false" ;;
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
    echo "FORMATTING"
    verusfmt $main_file
fi

echo "VEST CODEGEN" 
pushd $VESTPATH
cargo run -- $vest_file
popd

echo "COMPILING LIB FILE" 
pushd $ext_dir_path 
cargo build --lib
popd

echo "VERIFYING" 
verus -L dependency=$(realpath $ext_dir_path/target/debug/deps) $( find $ext_dir_path/target/debug/deps -name \*.rlib -exec realpath '{}' ';' | awk -F/ '{print "--extern " substr ($NF,4,index($NF,"-") - 4) "=" $0}' | grep -v vstd | grep -v builtin ) --multiple-errors=100 --rlimit=100 --no-lifetime $main_file 

echo "WARNING: currently using --no-lifetime for Verus"

