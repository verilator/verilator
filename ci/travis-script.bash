#!/usr/bin/env bash
# DESCRIPTION: Verilator: Travis CI main job script
#
# Copyright 2020 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# This is the main script executed in the 'script' phase by all jobs. We use a
# single script to keep the .travis.yml spec simple. We pass job parameters via
# environment variables using 'env' keys. Having different 'env' keys in jobs
# ensures they use different Travis build caches.
################################################################################

set -e
set -x

fatal() {
  echo "ERROR: $(basename "$0"): $1" >&2; exit 1;
}

if [ "$TRAVIS_OS_NAME" = "linux" ]; then
  export MAKE=make
  NPROC=$(nproc)
elif [ "$TRAVIS_OS_NAME" = "osx" ]; then
  export MAKE=make
  NPROC=$(sysctl -n hw.logicalcpu)
elif [ "$TRAVIS_OS_NAME" = "freebsd" ]; then
  export MAKE=gmake
  NPROC=$(sysctl -n hw.ncpu)
else
  fatal "Unknown os: '$TRAVIS_OS_NAME'"
fi

if [ "$TRAVIS_BUILD_STAGE_NAME" = "build" ]; then
  ##############################################################################
  # Build verilator

  if [ "$COVERAGE" != 1 ]; then
    autoconf
    ./configure --enable-longtests --enable-ccwarn
    "$MAKE" -j "$NPROC" -k
    if [ "$TRAVIS_OS_NAME" = "osx" ]; then
      file bin/verilator_bin
      file bin/verilator_bin_dbg
      md5 bin/verilator_bin
      md5 bin/verilator_bin_dbg
      stat bin/verilator_bin
      stat bin/verilator_bin_dbg
    fi
  else
    nodist/code_coverage --stages 1-2
  fi
elif [ "$TRAVIS_BUILD_STAGE_NAME" = "test" ]; then
  ##############################################################################
  # Run tests

  if [ "$TRAVIS_OS_NAME" = "osx" ]; then
    export VERILATOR_TEST_NO_GDB=1 # Pain to get GDB to work on OS X
    export VERILATOR_TEST_NO_GPROF=1 # Apple Clang has no -pg
    # export PATH="/Applications/gtkwave.app/Contents/Resources/bin:$PATH" # fst2vcd
    file bin/verilator_bin
    file bin/verilator_bin_dbg
    md5 bin/verilator_bin
    md5 bin/verilator_bin_dbg
    stat bin/verilator_bin
    stat bin/verilator_bin_dbg
    # For some reason, the dbg exe is corrupted by this point ('file' reports
    # it as data rather than a Mach-O). Unclear if this is an OS X issue or
    # one for Travis. Remove the file and re-link...
    rm bin/verilator_bin_dbg
    "$MAKE" -j "$NPROC" -k
  elif [ "$TRAVIS_OS_NAME" = "freebsd" ]; then
    export VERILATOR_TEST_NO_GDB=1 # Disable for now, ideally should run
    export VERILATOR_TEST_NO_GPROF=1 # gprof is a bit different on FreeBSD, disable
  fi

  # Run the specified test
  case $TESTS in
    dist-vlt-0)
      "$MAKE" -C test_regress SCENARIOS="--dist --vlt" DRIVER_HASHSET=--hashset=0/2
      ;;
    dist-vlt-1)
      "$MAKE" -C test_regress SCENARIOS="--dist --vlt" DRIVER_HASHSET=--hashset=1/2
      ;;
    vltmt-0)
      "$MAKE" -C test_regress SCENARIOS=--vltmt DRIVER_HASHSET=--hashset=0/2
      ;;
    vltmt-1)
      "$MAKE" -C test_regress SCENARIOS=--vltmt DRIVER_HASHSET=--hashset=1/2
      ;;
    coverage-dist)
      nodist/code_coverage --stages 3- --scenarios=--dist
      ;;
    coverage-vlt-0)
      nodist/code_coverage --stages 3- --scenarios=--vlt --hashset=0/4
      ;;
    coverage-vlt-1)
      nodist/code_coverage --stages 3- --scenarios=--vlt --hashset=1/4
      ;;
    coverage-vlt-2)
      nodist/code_coverage --stages 3- --scenarios=--vlt --hashset=2/4
      ;;
    coverage-vlt-3)
      nodist/code_coverage --stages 3- --scenarios=--vlt --hashset=3/4
      ;;
    coverage-vltmt-0)
      nodist/code_coverage --stages 3- --scenarios=--vltmt --hashset=0/4
      ;;
    coverage-vltmt-1)
      nodist/code_coverage --stages 3- --scenarios=--vltmt --hashset=1/4
      ;;
    coverage-vltmt-2)
      nodist/code_coverage --stages 3- --scenarios=--vltmt --hashset=2/4
      ;;
    coverage-vltmt-3)
      nodist/code_coverage --stages 3- --scenarios=--vltmt --hashset=3/4
      ;;
    *)
      fatal "Unknown test: $TESTS"
      ;;
  esac
  # Upload coverage data to codecov.io
  if [[ $TESTS == coverage-* ]]; then
    bash <(curl -s https://codecov.io/bash) -f nodist/obj_dir/coverage/app_total.info
  fi
else
  ##############################################################################
  # Unknown build stage
  fatal "Unknown build stage: '$TRAVIS_BUILD_STAGE_NAME'"
fi
