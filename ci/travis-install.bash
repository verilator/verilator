#!/usr/bin/env bash
# DESCRIPTION: Verilator: Travis CI dependency install script
#
# Copyright 2020 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# This script runs in the 'install' phase of all jobs, in all stages. We try to
# minimize the time spent in this by selectively installing only the components
# required by the particular build stage.
################################################################################

# Note that Travis runs "apt-get update" when "apt-get install" is used in the
# .travis.yml file directly, but since we invoke it via this script, we need to
# run it manually where requried, otherwise some packages cannot be found.

set -e
set -x

fatal() {
  echo "ERROR: $(basename "$0"): $1" >&2; exit 1;
}

install-vcddiff() {
  TMP_DIR="$(mktemp -d)"
  git clone https://github.com/veripool/vcddiff "$TMP_DIR"
  git -C "${TMP_DIR}" checkout 5112f88b7ba8818dce9dfb72619e64a1fc19542c
  make -C "${TMP_DIR}"
  sudo cp "${TMP_DIR}/vcddiff" /usr/local/bin
}

if [ "$TRAVIS_BUILD_STAGE_NAME" = "build" ]; then
  ##############################################################################
  # Dependencies of jobs in the 'build' stage, i.e.: packages required to
  # build Verilator

  if [ "$TRAVIS_OS_NAME" = "linux" ]; then
    time sudo apt-get update
    sudo apt-get install libfl-dev
    sudo apt-get install libgoogle-perftools-dev
    if [ "$COVERAGE" = 1 ]; then
      yes yes | sudo cpan -fi Unix::Processors Parallel::Forker
    fi
  else
    fatal "Unknown os: '$TRAVIS_OS_NAME'"
  fi
elif [ "$TRAVIS_BUILD_STAGE_NAME" = "test" ]; then
  ##############################################################################
  # Dependencies of jobs in the 'test' stage, i.e.: packages required to
  # run the tests

  if [ "$TRAVIS_OS_NAME" = "linux" ]; then
    sudo apt-get update
    sudo apt-get install gdb gtkwave lcov
    if [ "$TRAVIS_DIST" = "focal" ]; then
      sudo apt-get install libsystemc-dev
    fi
    yes yes | sudo cpan -fi Unix::Processors Parallel::Forker
    # Not listing Bit::Vector as slow to install, and only skips one test
    install-vcddiff
  else
    fatal "Unknown os: '$TRAVIS_OS_NAME'"
  fi
else
  ##############################################################################
  # Unknown build stage
  fatal "Unknown build stage: '$TRAVIS_BUILD_STAGE_NAME'"
fi
