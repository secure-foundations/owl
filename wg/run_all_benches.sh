#!/bin/bash

set -euxo pipefail

function usage() {
    echo "Usage: ${0} [-s] SUFFIX [-g] VANILLA_WG_GO_PATH"
    echo "-s SUFFIX" will suffix the output directories with SUFFIX
    exit 2
}

fd_suffix=""
vanilla_wg_go_path="${VANILLA_WG_GO_PATH}"

while getopts "s:g:" opt; do
    case "${opt}" in
        s) fd_suffix="${OPTARG}" ;;
        \? ) usage ;;
        : ) usage ;;
    esac
done

wg_rs_bin=$(realpath "./wireguard-rs/target/release/wireguard-rs")
owl_wg_go_bin=$(realpath "./wireguard-go/wireguard-go")
vanilla_wg_go_bin=$(realpath "$vanilla_wg_go_path/wireguard-go")
sleep=10

## prompt for sudo password if necessary
sudo echo "sudo available"


## run wireguard-rs benchmarks with verified crypto

pushd wireguard-rs
cargo build --release
popd

sudo ./run-linedelay-test.sh -s "$fd_suffix-wg_rs_baseline_verifcrypto" $wg_rs_bin
sleep $sleep
sudo ./run-iperf-test.sh -s "$fd_suffix-wg_rs_baseline_verifcrypto" $wg_rs_bin
sleep $sleep
sudo ./run-linedelay-test.sh -o -s "$fd_suffix-wg_rs_owl_verifcrypto" $wg_rs_bin
sleep $sleep
sudo ./run-iperf-test.sh -o -s "$fd_suffix-wg_rs_owl_verifcrypto" $wg_rs_bin
sleep $sleep

## run wireguard-rs benchmarks with baseline crypto

pushd wireguard-rs
cargo build --release --features=nonverif-crypto
popd

sudo ./run-linedelay-test.sh -s "$fd_suffix-wg_rs_baseline_nonverifcrypto" $wg_rs_bin
sleep $sleep
sudo ./run-iperf-test.sh -s "$fd_suffix-wg_rs_baseline_nonverifcrypto" $wg_rs_bin
sleep $sleep
sudo ./run-linedelay-test.sh -o -s "$fd_suffix-wg_rs_owl_nonverifcrypto" $wg_rs_bin
sleep $sleep
sudo ./run-iperf-test.sh -o -s "$fd_suffix-wg_rs_owl_nonverifcrypto" $wg_rs_bin
sleep $sleep

## run wireguard-go-owl benchmarks with verified crypto

pushd wireguard-go
make clean
make wireguard-go 
popd

sudo ./run-linedelay-test.sh -s "$fd_suffix-wg_go_owl_verifcrypto" $owl_wg_go_bin
sleep $sleep
sudo ./run-iperf-test.sh -s "$fd_suffix-wg_go_owl_verifcrypto" $owl_wg_go_bin
sleep $sleep

## run wireguard-go-owl benchmarks with baseline crypto

pushd wireguard-go
make clean
make wireguard-go RUSTLIB_ARGS="--features nonverif-crypto"
popd

sudo ./run-linedelay-test.sh -s "$fd_suffix-wg_go_owl_nonverifcrypto" $owl_wg_go_bin
sleep $sleep
sudo ./run-iperf-test.sh -s "$fd_suffix-wg_go_owl_nonverifcrypto" $owl_wg_go_bin
sleep $sleep

## run wireguard-go baseline benchmarks

pushd $vanilla_wg_go_path
make clean
make wireguard-go
popd

sudo ./run-linedelay-test.sh -s "$fd_suffix-wg_go_baseline" $vanilla_wg_go_bin
sleep $sleep
sudo ./run-iperf-test.sh -s "$fd_suffix-wg_go_baseline" $vanilla_wg_go_bin
sleep $sleep




