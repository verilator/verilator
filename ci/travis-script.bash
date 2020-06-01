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

if [ "$TRAVIS_BUILD_STAGE_NAME" = "build" ]; then
  ##############################################################################
  # Build verilator

  if [ "$TRAVIS_OS_NAME" = "linux" ]; then
    if [ "$COVERAGE" != 1 ]; then
      autoconf
      ./configure --enable-longtests --enable-ccwarn
      make -j $(nproc)
    else
      nodist/code_coverage --stages 1-2
    fi
  else
    fatal "Unknown os: '$TRAVIS_OS_NAME'"
  fi
elif [ "$TRAVIS_BUILD_STAGE_NAME" = "test" ]; then
  ##############################################################################
  # Run tests

  if [ "$TRAVIS_OS_NAME" = "linux" ]; then
    # Run the specified test
    case $TESTS in
      dist)
        make -C test_regress SCENARIOS=--dist
        ;;
      vlt0)
        make -C test_regress SCENARIOS=--vlt DRIVER_HASHSET=--hashset=0/2
        ;;
      vlt1)
        make -C test_regress SCENARIOS=--vlt DRIVER_HASHSET=--hashset=1/2
        ;;
      vltmt0)
        make -C test_regress SCENARIOS=--vltmt DRIVER_HASHSET=--hashset=0/2
        ;;
      vltmt1)
        make -C test_regress SCENARIOS=--vltmt DRIVER_HASHSET=--hashset=1/2
        ;;
      coverage-dist)
        nodist/code_coverage --stages 3- --scenarios=--dist
        ;;
      coverage-vlt0)
        nodist/code_coverage --stages 3- --scenarios=--vlt --hashset=0/4
        ;;
      coverage-vlt1)
        nodist/code_coverage --stages 3- --scenarios=--vlt --hashset=1/4
        ;;
      coverage-vlt2)
        nodist/code_coverage --stages 3- --scenarios=--vlt --hashset=2/4
        ;;
      coverage-vlt3)
        nodist/code_coverage --stages 3- --scenarios=--vlt --hashset=3/4
        ;;
      coverage-vltmt0)
        nodist/code_coverage --stages 3- --scenarios=--vltmt --hashset=0/4
        ;;
      coverage-vltmt1)
        nodist/code_coverage --stages 3- --scenarios=--vltmt --hashset=1/4
        ;;
      coverage-vltmt2)
        nodist/code_coverage --stages 3- --scenarios=--vltmt --hashset=2/4
        ;;
      coverage-vltmt3)
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
    fatal "Unknown os: '$TRAVIS_OS_NAME'"
  fi
else
  ##############################################################################
  # Unknown build stage
  fatal "Unknown build stage: '$TRAVIS_BUILD_STAGE_NAME'"
fi
