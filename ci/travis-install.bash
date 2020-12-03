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

if [ "$TRAVIS_OS_NAME" = "linux" ]; then
  MAKE=make
elif [ "$TRAVIS_OS_NAME" = "osx" ]; then
  MAKE=make
elif [ "$TRAVIS_OS_NAME" = "freebsd" ]; then
  MAKE=gmake
else
  fatal "Unknown os: '$TRAVIS_OS_NAME'"
fi

install-vcddiff() {
  TMP_DIR="$(mktemp -d)"
  git clone https://github.com/veripool/vcddiff "$TMP_DIR"
  git -C "${TMP_DIR}" checkout 5112f88b7ba8818dce9dfb72619e64a1fc19542c
  "$MAKE" -C "${TMP_DIR}"
  sudo cp "${TMP_DIR}/vcddiff" /usr/local/bin
}

if [ "$TRAVIS_BUILD_STAGE_NAME" = "build" ]; then
  ##############################################################################
  # Dependencies of jobs in the 'build' stage, i.e.: packages required to
  # build Verilator

  if [ "$TRAVIS_OS_NAME" = "linux" ]; then
    sudo apt-get update
    sudo apt-get install libfl-dev
    sudo apt-get install libgoogle-perftools-dev
    if [ "$COVERAGE" = 1 ]; then
      yes yes | sudo cpan -fi Unix::Processors Parallel::Forker
    fi
    if [ "$M32" = 1 ]; then
      sudo apt-get install gcc-multilib g++-multilib
    fi
  elif [ "$TRAVIS_OS_NAME" = "osx" ]; then
    brew update
    brew install ccache perl gperftools
  elif [ "$TRAVIS_OS_NAME" = "freebsd" ]; then
    sudo pkg install -y autoconf bison ccache gmake perl5
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
    if [ "$M32" = 1 ]; then
      sudo apt-get install lib32z1-dev gcc-multilib g++-multilib
    fi
  elif [ "$TRAVIS_OS_NAME" = "osx" ]; then
    brew update
    # brew cask install gtkwave # fst2vcd hangs at launch, so don't bother
    brew install ccache perl
  elif [ "$TRAVIS_OS_NAME" = "freebsd" ]; then
    # fst2vcd fails with "Could not open '<input file>', exiting."
    sudo pkg install -y ccache gmake perl5 python3
  else
    fatal "Unknown os: '$TRAVIS_OS_NAME'"
  fi
  # Common installs
  if [ "$TRAVIS_DIST" != "trusty" ]; then
    TRAVIS_CPAN_REPO=https://cpan.org
  fi
  yes yes | sudo cpan -M $TRAVIS_CPAN_REPO -fi Unix::Processors Parallel::Forker
  install-vcddiff
else
  ##############################################################################
  # Unknown build stage
  fatal "Unknown build stage: '$TRAVIS_BUILD_STAGE_NAME'"
fi
