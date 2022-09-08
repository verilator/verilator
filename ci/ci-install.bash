#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI dependency install script
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

set -e
set -x

cd $(dirname "$0")/..

# Avoid occasional cpan failures "Issued certificate has expired."
export PERL_LWP_SSL_VERIFY_HOSTNAME=0
echo "check_certificate = off" >> ~/.wgetrc

fatal() {
  echo "ERROR: $(basename "$0"): $1" >&2; exit 1;
}

if [ "$CI_M32" = "0" ]; then
  unset CI_M32
elif [ "$CI_M32" != "1" ]; then
  fatal "\$CI_M32 must be '0' or '1'";
fi

if [ "$CI_OS_NAME" = "linux" ]; then
  MAKE=make
elif [ "$CI_OS_NAME" = "osx" ]; then
  MAKE=make
elif [ "$CI_OS_NAME" = "freebsd" ]; then
  MAKE=gmake
else
  fatal "Unknown os: '$CI_OS_NAME'"
fi

install-vcddiff() {
  TMP_DIR="$(mktemp -d)"
  git clone https://github.com/veripool/vcddiff "$TMP_DIR"
  git -C "${TMP_DIR}" checkout e5664be5fe39d353bf3fcb50aa05214ab7ed4ac4
  "$MAKE" -C "${TMP_DIR}"
  sudo cp "${TMP_DIR}/vcddiff" /usr/local/bin
}

if [ "$CI_BUILD_STAGE_NAME" = "build" ]; then
  ##############################################################################
  # Dependencies of jobs in the 'build' stage, i.e.: packages required to
  # build Verilator

  if [ "$CI_OS_NAME" = "linux" ]; then
    sudo apt-get update
    sudo apt-get install libfl-dev ccache
    if [ "$CI_RUNS_ON" != "ubuntu-22.04" ]; then
      # Some conflict of libunwind verison on 22.04, can live without it for now
      sudo apt-get install libgoogle-perftools-dev
    fi
    if [ "$CI_RUNS_ON" = "ubuntu-20.04" ] || [ "$CI_RUNS_ON" = "ubuntu-22.04" ]; then
      sudo apt-get install libsystemc libsystemc-dev
    fi
    if [ "$COVERAGE" = 1 ]; then
      yes yes | sudo cpan -fi Parallel::Forker
    fi
    if [ "$CI_M32" = 1 ]; then
      sudo apt-get install gcc-multilib g++-multilib
    fi
  elif [ "$CI_OS_NAME" = "osx" ]; then
    brew update
    brew install ccache perl gperftools
  elif [ "$CI_OS_NAME" = "freebsd" ]; then
    sudo pkg install -y autoconf bison ccache gmake perl5
  else
    fatal "Unknown os: '$CI_OS_NAME'"
  fi

  if [ -n "$CCACHE_DIR" ]; then
    mkdir -p "$CCACHE_DIR" && ./ci/ci-ccache-maint.bash
  fi
elif [ "$CI_BUILD_STAGE_NAME" = "test" ]; then
  ##############################################################################
  # Dependencies of jobs in the 'test' stage, i.e.: packages required to
  # run the tests

  if [ "$CI_OS_NAME" = "linux" ]; then
    sudo apt-get update
    # libfl-dev needed for internal coverage's test runs
    sudo apt-get install gdb gtkwave lcov libfl-dev ccache
    if [ "$CI_RUNS_ON" = "ubuntu-20.04" ] || [ "$CI_RUNS_ON" = "ubuntu-22.04" ]; then
      sudo apt-get install libsystemc-dev
    fi
    if [ "$CI_M32" = 1 ]; then
      sudo apt-get install lib32z1-dev gcc-multilib g++-multilib
    fi
  elif [ "$CI_OS_NAME" = "osx" ]; then
    brew update
    # brew cask install gtkwave # fst2vcd hangs at launch, so don't bother
    brew install ccache perl
  elif [ "$CI_OS_NAME" = "freebsd" ]; then
    # fst2vcd fails with "Could not open '<input file>', exiting."
    sudo pkg install -y ccache gmake perl5 python3
  else
    fatal "Unknown os: '$CI_OS_NAME'"
  fi
  # Common installs
  if [ "$CI_RUNS_ON" != "ubuntu-14.04" ]; then
    CI_CPAN_REPO=https://cpan.org
  fi
  yes yes | sudo cpan -M $CI_CPAN_REPO -fi Parallel::Forker
  install-vcddiff
else
  ##############################################################################
  # Unknown build stage
  fatal "Unknown build stage: '$CI_BUILD_STAGE_NAME'"
fi
