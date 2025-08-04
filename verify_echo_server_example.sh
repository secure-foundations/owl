#!/bin/bash

set -euo pipefail

if [ "$#" -ne 0 ]; then
    echo "Usage: $0"
    exit 1
fi

docker run -it --rm -v $(pwd):/root/owlc/ --workdir /root/owlc/echo_server_example/extraction/ owlc-aeval ./run_verus.sh

