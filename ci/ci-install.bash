#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI dependency install script
#
# SPDX-FileCopyrightText: 2020 Geza Lore
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

if [ "$CI_OS_NAME" = "linux" ]; then
  MAKE=make
elif [ "$CI_OS_NAME" = "osx" ]; then
  MAKE=make
elif [ "$CI_OS_NAME" = "freebsd" ]; then
  MAKE=gmake
else
  fatal "Unknown CI_OS_NAME: '$CI_OS_NAME'"
fi

if [ "$CI_OS_NAME" = "linux" ]; then
  # Avoid slow "processing triggers for man db"
  echo "path-exclude /usr/share/doc/*"  | sudo tee -a /etc/dpkg/dpkg.cfg.d/01_nodoc
  echo "path-exclude /usr/share/man/*"  | sudo tee -a /etc/dpkg/dpkg.cfg.d/01_nodoc
  echo "path-exclude /usr/share/info/*" | sudo tee -a /etc/dpkg/dpkg.cfg.d/01_nodoc
fi

install-vcddiff() {
  TMP_DIR="$(mktemp -d)"
  git clone https://github.com/veripool/vcddiff "$TMP_DIR"
  git -C "${TMP_DIR}" checkout 4db0d84a27e8f148b127e916fc71d650837955c5
  "$MAKE" -C "${TMP_DIR}"
  sudo cp "${TMP_DIR}/vcddiff" /usr/local/bin
}

if [ "$CI_BUILD_STAGE_NAME" = "build" ]; then
  ##############################################################################
  # Dependencies of jobs in the 'build' stage, i.e.: packages required to
  # build Verilator

  if [ "$CI_OS_NAME" = "linux" ]; then
    sudo apt-get update ||
    sudo apt-get update
    sudo apt-get install --yes ccache help2man libfl-dev ||
    sudo apt-get install --yes ccache help2man libfl-dev
    if [[ ! "$CI_RUNS_ON" =~ "ubuntu-22.04" ]]; then
      # Some conflict of libunwind verison on 22.04, can live without it for now
      sudo apt-get install --yes libjemalloc-dev ||
      sudo apt-get install --yes libjemalloc-dev
    fi
    if [[ "$CI_RUNS_ON" =~ "ubuntu-22.04" ]] || [[ "$CI_RUNS_ON" =~ "ubuntu-24.04" ]] || [[ "$CI_RUNS_ON" =~ "ubuntu-26.04" ]]; then
      if [[ ! "$CI_RUNS_ON" =~ "-riscv" ]]; then
        sudo apt-get install --yes libsystemc libsystemc-dev ||
        sudo apt-get install --yes libsystemc libsystemc-dev
      fi
    fi
    if [[ "$CI_RUNS_ON" =~ "ubuntu-22.04" ]] || [[ "$CI_RUNS_ON" =~ "ubuntu-24.04" ]] || [[ "$CI_RUNS_ON" =~ "ubuntu-26.04" ]]; then
      sudo apt-get install --yes bear mold ||
      sudo apt-get install --yes bear mold
    fi
  elif [ "$CI_OS_NAME" = "osx" ]; then
    brew update ||
    brew update
    brew install ccache perl gperftools autoconf bison flex help2man ||
    brew install ccache perl gperftools autoconf bison flex help2man
  elif [ "$CI_OS_NAME" = "freebsd" ]; then
    sudo pkg install -y autoconf bison ccache gmake perl5
  else
    fatal "Unknown CI_OS_NAME: '$CI_OS_NAME'"
  fi

  if [ -n "$CCACHE_DIR" ]; then
    mkdir -p "$CCACHE_DIR"
  fi
elif [ "$CI_BUILD_STAGE_NAME" = "test" ]; then
  ##############################################################################
  # Dependencies of jobs in the 'test' stage, i.e.: packages required to
  # run the tests

  if [ "$CI_OS_NAME" = "linux" ]; then
    sudo apt-get update ||
    sudo apt-get update
    # libfl-dev needed for internal coverage's test runs
    sudo apt-get install --yes gdb gtkwave lcov libfl-dev ccache jq z3 ||
    sudo apt-get install --yes gdb gtkwave lcov libfl-dev ccache jq z3
    # Required for test_regress/t/t_dist_attributes.py
    if [[ "$CI_RUNS_ON" =~ "ubuntu-22.04" ]] || [[ "$CI_RUNS_ON" =~ "ubuntu-24.04" ]] || [[ "$CI_RUNS_ON" =~ "ubuntu-26.04" ]]; then
      sudo apt-get install --yes python3-clang mold ||
      sudo apt-get install --yes python3-clang mold
    fi
    if [[ "$CI_RUNS_ON" =~ "ubuntu-22.04" ]] || [[ "$CI_RUNS_ON" =~ "ubuntu-24.04" ]] || [[ "$CI_RUNS_ON" =~ "ubuntu-26.04" ]]; then
      if [[ ! "$CI_RUNS_ON" =~ "-riscv" ]]; then
        sudo apt-get install --yes libsystemc libsystemc-dev ||
        sudo apt-get install --yes libsystemc libsystemc-dev
      fi
    fi
  elif [ "$CI_OS_NAME" = "osx" ]; then
    brew update
    # brew cask install gtkwave # fst2vcd hangs at launch, so don't bother
    brew install ccache perl jq z3
  elif [ "$CI_OS_NAME" = "freebsd" ]; then
    # fst2vcd fails with "Could not open '<input file>', exiting."
    sudo pkg install -y ccache gmake perl5 python3 jq z3
  else
    fatal "Unknown CI_OS_NAME: '$CI_OS_NAME'"
  fi
  # Common installs
  install-vcddiff
  # Workaround -fsanitize=address crash
  sudo sysctl -w vm.mmap_rnd_bits=28
else
  ##############################################################################
  # Unknown build stage
  fatal "Unknown CI_BUILD_STAGE_NAME: '$CI_BUILD_STAGE_NAME'"
fi
