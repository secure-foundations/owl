#!/bin/bash

# This script deletes the network configuration set up by setup-netconfig.sh

set -euo pipefail

# Delete net1 namespace. This deletes veth1n and wg1n interfaces too
ip netns del net1

# Delete veth1 interface
ip link del veth1

# Delete wg1 interface
ip link del wg1