#!/bin/bash

set -e

if [ "$#" -ne 1 ]; then
    echo "Use: '$0 <test_name>'" >&2
    echo "e.g.: '$0 d1'>" >&2
    exit 1
fi

NAME="$1"

echo "=====Compiling====="
$VERILATOR4 --binary -O0 --four-state --trace-vcd -Wno-fatal "${NAME}.sv"

echo "=====Running======="
./obj_dir/V"${NAME}" |& tee "${NAME}.tmp"

cat "${NAME}.tmp" | head -n -4 > "${NAME}.log"

if diff "${NAME}.log" "${NAME}.out"; then
    echo 'Demo Finished!'
else
    echo 'Demo failed'
fi
