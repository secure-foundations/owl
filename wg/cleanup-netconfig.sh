#!/bin/bash

# This script deletes the network configuration set up by setup-netconfig.sh

set -euo pipefail

# Delete wg1 interface
ip link del wg1
ip netns exec net1 ip link del wg1n

# Delete veth1 interface
ip link del veth1

# Delete net1 namespace. This deletes veth1n interface too
ip netns del net1


