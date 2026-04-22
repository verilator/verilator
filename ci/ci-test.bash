#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI test job script
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# Executed in the 'test' stage.
################################################################################

# Destructive to the checkout (wipes most of it); never run locally
if [ "$GITHUB_ACTIONS" != "true" ]; then
  echo "ERROR: $(basename "$0") must only be run in GitHub Actions CI" >&2
  exit 1
fi

set -e
set -x

source "$(dirname "$0")/ci-common.bash"

################################################################################
# Parse arguments

OPT_RELOC=
OPT_SUITE=
while [ $# -gt 0 ]; do
  case "$1" in
    --reloc)
      [ $# -ge 2 ] || fatal "--reloc requires an argument"
      OPT_RELOC="$2"
      shift
      ;;
    --suite)
      [ $# -ge 2 ] || fatal "--suite requires an argument"
      OPT_SUITE="$2"
      shift
      ;;
    *) fatal "Unknown option: '$1'" ;;
  esac
  shift
done

[ -n "$OPT_SUITE" ] || fatal "--suite is required"

################################################################################
# Run tests

export VERILATOR_TEST_NO_CONTRIBUTORS=1  # Separate workflow check
export VERILATOR_TEST_NO_LINT_PY=1  # Separate workflow check

if [ "$HOST_OS" = "macOS" ]; then
  export VERILATOR_TEST_NO_GDB=1  # No working GDB on macOS
fi

TEST_REGRESS=test_regress
if [ -n "$OPT_RELOC" ]; then
  # Testing that the installation is relocatable.
  "$MAKE" install
  # Install prefix, as configured into the Makefile at build time
  INSTALL_DIR=$(sed -n 's/^prefix = //p' Makefile)
  mkdir -p "$OPT_RELOC"
  mv "$INSTALL_DIR" "$OPT_RELOC/relocated-install"
  export VERILATOR_ROOT="$OPT_RELOC/relocated-install/share/verilator"
  TEST_REGRESS="$OPT_RELOC/test_regress"
  mv test_regress "$TEST_REGRESS"
  NODIST="$OPT_RELOC/nodist"
  mv nodist "$NODIST"
  # Delete everything else, but keep the CI infrastructure
  find . -mindepth 1 -maxdepth 1 ! -name .github ! -name ci -exec rm -rf {} +
  ls -la .
fi

# Run the specified suite
ccache -z
TEST_START=$SECONDS
case $OPT_SUITE in
  dist-vlt-0)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--dist --vlt --driver-clean" DRIVER_HASHSET=--hashset=0/4
    ;;
  dist-vlt-1)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--dist --vlt --driver-clean" DRIVER_HASHSET=--hashset=1/4
    ;;
  dist-vlt-2)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--dist --vlt --driver-clean" DRIVER_HASHSET=--hashset=2/4
    ;;
  dist-vlt-3)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--dist --vlt --driver-clean" DRIVER_HASHSET=--hashset=3/4
    ;;
  vltmt-0)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt --driver-clean" DRIVER_HASHSET=--hashset=0/3
    ;;
  vltmt-1)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt --driver-clean" DRIVER_HASHSET=--hashset=1/3
    ;;
  vltmt-2)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt --driver-clean" DRIVER_HASHSET=--hashset=2/3
    ;;
  dist-vlt4-0)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--dist --vlt4 --driver-clean" DRIVER_HASHSET=--hashset=0/4
    ;;
  dist-vlt4-1)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--dist --vlt4 --driver-clean" DRIVER_HASHSET=--hashset=1/4
    ;;
  dist-vlt4-2)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--dist --vlt4 --driver-clean" DRIVER_HASHSET=--hashset=2/4
    ;;
  dist-vlt4-3)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--dist --vlt4 --driver-clean" DRIVER_HASHSET=--hashset=3/4
    ;;
  vltmt4-0)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4 --driver-clean" DRIVER_HASHSET=--hashset=0/3
    ;;
  vltmt4-1)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4 --driver-clean" DRIVER_HASHSET=--hashset=1/3
    ;;
  vltmt4-2)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4 --driver-clean" DRIVER_HASHSET=--hashset=2/3
    ;;
  coverage-dist)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--dist"
    ;;
  coverage-vlt-0)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=0/10
    ;;
  coverage-vlt-1)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=1/10
    ;;
  coverage-vlt-2)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=2/10
    ;;
  coverage-vlt-3)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=3/10
    ;;
  coverage-vlt-4)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=4/10
    ;;
  coverage-vlt-5)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=5/10
    ;;
  coverage-vlt-6)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=6/10
    ;;
  coverage-vlt-7)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=7/10
    ;;
  coverage-vlt-8)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=8/10
    ;;
  coverage-vlt-9)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=9/10
    ;;
  coverage-vltmt-0)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=0/10
    ;;
  coverage-vltmt-1)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=1/10
    ;;
  coverage-vltmt-2)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=2/10
    ;;
  coverage-vltmt-3)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=3/10
    ;;
  coverage-vltmt-4)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=4/10
    ;;
  coverage-vltmt-5)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=5/10
    ;;
  coverage-vltmt-6)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=6/10
    ;;
  coverage-vltmt-7)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=7/10
    ;;
  coverage-vltmt-8)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=8/10
    ;;
  coverage-vltmt-9)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=9/10
    ;;
  coverage-vlt4-0)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=0/10
    ;;
  coverage-vlt4-1)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=1/10
    ;;
  coverage-vlt4-2)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=2/10
    ;;
  coverage-vlt4-3)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=3/10
    ;;
  coverage-vlt4-4)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=4/10
    ;;
  coverage-vlt4-5)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=5/10
    ;;
  coverage-vlt4-6)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=6/10
    ;;
  coverage-vlt4-7)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=7/10
    ;;
  coverage-vlt4-8)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=8/10
    ;;
  coverage-vlt4-9)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vlt4" DRIVER_HASHSET=--hashset=9/10
    ;;
  coverage-vltmt4-0)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=0/10
    ;;
  coverage-vltmt4-1)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=1/10
    ;;
  coverage-vltmt4-2)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=2/10
    ;;
  coverage-vltmt4-3)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=3/10
    ;;
  coverage-vltmt4-4)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=4/10
    ;;
  coverage-vltmt4-5)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=5/10
    ;;
  coverage-vltmt4-6)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=6/10
    ;;
  coverage-vltmt4-7)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=7/10
    ;;
  coverage-vltmt4-8)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=8/10
    ;;
  coverage-vltmt4-9)
    "$MAKE" -C "$TEST_REGRESS" SCENARIOS="--vltmt4" DRIVER_HASHSET=--hashset=9/10
    ;;
  *)
    fatal "Unknown suite: $OPT_SUITE"
    ;;
esac
ccache -svv
ccache --evict-older-than "$((SECONDS - TEST_START + 60))s"
ccache -svv
uptime # To see load average
