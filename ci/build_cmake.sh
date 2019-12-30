#!/bin/bash
# DESCRIPTION: Verilator: Travis CI cmake build script
#
# Copyright 2019 by Todd Strader. This program is free software; you can
# redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.

set -e

if [ "$TRAVIS_OS_NAME" != "windows" ]; then
    # This script is currently only used on Windows
    exit 0
fi

if [ -z "${VERILATOR_ROOT}" ]; then
    echo "VERILATOR_ROOT not set"
    exit -1
fi

echo "Building Verilator"

# Unsure why Travis monkies with the capitalization of the stage name, but it does
if [[ -n ${TRAVIS_BUILD_STAGE_NAME} && \
     ${TRAVIS_BUILD_STAGE_NAME} != "Build verilator" ]]; then
  echo "WARNING: Building Verilator in Travis build stage other than \"Build verilator\": ${TRAVIS_BUILD_STAGE_NAME}"
fi

VERILATOR_BUILD="${VERILATOR_ROOT}/../build-verilator"

cmake \
    -G Ninja \
    -S "${VERILATOR_ROOT}" \
    -B "${VERILATOR_BUILD}" \
    -DCMAKE_PROGRAM_PATH="C:/Perl64/bin"

cmake --build "${VERILATOR_BUILD}"
