#!/bin/bash
# DESCRIPTION: Verilator: Travis CI build script
#
# Copyright 2019 by Todd Strader. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
# This script builds and caches the Verilator binaries for Travis CI
# (and possibly other CI platforms).  The Verilator CI system uses this
# script, but other CI systems that depend on Verilator may also use
# the script.
# see: https://github.com/verilator/verilator_ext_tests/blob/master/.travis.yml
# To use this script, either checkout Verilator as part of the CI build
# process or add Verilator as a Git submodule.  Verilator tarballs can
# not be used as the script relies on Git revisions for caching.
set -e

if [ -z "${VERILATOR_NUM_JOBS}" ]; then
    VERILATOR_NUM_JOBS=$(nproc)
fi

# Caching would be simpler if we installed without VERILATOR_ROOT, but
#   it's needed for driver.pl outside of the repo
if [ -z "${VERILATOR_ROOT}" ]; then
    echo "VERILATOR_ROOT not set"
    exit -1
fi

if [ -z "${VERILATOR_CACHE}" ]; then
    echo "VERILATOR_CACHE not set"
    exit -1
fi

VERILATOR_REV=$(cd "${VERILATOR_ROOT}" && git rev-parse HEAD)
echo "Found Verilator rev ${VERILATOR_REV}"

CACHED_REV_FILE=${VERILATOR_CACHE}/.rev.txt

if [[ ! -f "${CACHED_REV_FILE}" || \
      $(< "${CACHED_REV_FILE}") != "${VERILATOR_REV}" ]]; then
    echo "Building Verilator"

    # Unsure why Travis monkies with the capitalization of the stage name, but it does
    if [[ -n ${TRAVIS_BUILD_STAGE_NAME} && \
         ${TRAVIS_BUILD_STAGE_NAME} != "Build verilator" ]]; then
      echo "WARNING: Building Verilator in Travis build stage other than \"Build verilator\": ${TRAVIS_BUILD_STAGE_NAME}"
    fi

    cd "${VERILATOR_ROOT}"
    autoconf && ./configure ${VERILATOR_CONFIG_FLAGS} && make -j ${VERILATOR_NUM_JOBS}
    # Copy the Verilator build artifacts
    mkdir -p "${VERILATOR_CACHE}"
    rm -rf ${VERILATOR_CACHE}/*
    cp bin/*bin* "${VERILATOR_CACHE}"
    # Remember the Git revision
    echo "${VERILATOR_REV}" > "${CACHED_REV_FILE}"
else
    echo "Using cached Verilator"
    cd "${VERILATOR_ROOT}"
    # Create include/verilated_config.h and maybe other things
    autoconf && ./configure ${VERILATOR_CONFIG_FLAGS}
    cp ${VERILATOR_CACHE}/* bin
fi
