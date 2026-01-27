#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI main job script
#
# SPDX-FileCopyrightText: 2020 Geza Lore
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# This is the main script executed in the 'script' phase by all jobs. We use a
# single script to keep the CI setting simple. We pass job parameters via
# environment variables using 'env' keys.
################################################################################

set -e
set -x

fatal() {
  echo "ERROR: $(basename "$0"): $1" >&2; exit 1;
}

if [ "$CI_OS_NAME" = "linux" ]; then
  export MAKE=make
  NPROC=$(nproc)
elif [ "$CI_OS_NAME" = "osx" ]; then
  export MAKE=make
  NPROC=$(sysctl -n hw.logicalcpu)
  # Disable ccache, doesn't always work in GitHub Actions
  export OBJCACHE=
elif [ "$CI_OS_NAME" = "freebsd" ]; then
  export MAKE=gmake
  NPROC=$(sysctl -n hw.ncpu)
else
  fatal "Unknown os: '$CI_OS_NAME'"
fi
NPROC=$(expr $NPROC '+' 1)

if [ "$CI_BUILD_STAGE_NAME" = "build" ]; then
  ##############################################################################
  # Build verilator

  autoconf
  CONFIGURE_ARGS="--enable-longtests --enable-ccwarn"
  if [ "$CI_DEV_ASAN" = 1 ]; then
    CONFIGURE_ARGS="$CONFIGURE_ARGS --enable-dev-asan"
    CXX="$CXX -DVL_LEAK_CHECKS"
  fi
  if [ "$CI_DEV_GCOV" = 1 ]; then
    CONFIGURE_ARGS="$CONFIGURE_ARGS --enable-dev-gcov"
  fi
  ./configure $CONFIGURE_ARGS --prefix="$INSTALL_DIR"
  ccache -z
  "$MAKE" -j "$NPROC" -k
  # 22.04: ccache -s -v
  ccache -s
  if [ "$CI_OS_NAME" = "osx" ]; then
    file bin/verilator_bin
    file bin/verilator_bin_dbg
    md5 bin/verilator_bin
    md5 bin/verilator_bin_dbg
    stat bin/verilator_bin
    stat bin/verilator_bin_dbg
  fi
elif [ "$CI_BUILD_STAGE_NAME" = "test" ]; then
  ##############################################################################
  # Run tests

  export VERILATOR_TEST_NO_CONTRIBUTORS=1  # Separate workflow check
  export VERILATOR_TEST_NO_LINT_PY=1  # Separate workflow check

  if [ "$CI_OS_NAME" = "osx" ]; then
    export VERILATOR_TEST_NO_GDB=1  # Pain to get GDB to work on OS X
    # TODO below may no longer be required as configure checks for -pg
    export VERILATOR_TEST_NO_GPROF=1  # Apple Clang has no -pg
    # export PATH="/Applications/gtkwave.app/Contents/Resources/bin:$PATH" # fst2vcd
    file bin/verilator_bin
    file bin/verilator_bin_dbg
    md5 bin/verilator_bin
    md5 bin/verilator_bin_dbg
    stat bin/verilator_bin
    stat bin/verilator_bin_dbg
    # For some reason, the dbg exe is corrupted by this point ('file' reports
    # it as data rather than a Mach-O). Unclear if this is an OS X issue or
    # CI's. Remove the file and re-link...
    rm bin/verilator_bin_dbg
    "$MAKE" -j "$NPROC" -k
  elif [ "$CI_OS_NAME" = "freebsd" ]; then
    export VERILATOR_TEST_NO_GDB=1 # Disable for now, ideally should run
    # TODO below may no longer be required as configure checks for -pg
    export VERILATOR_TEST_NO_GPROF=1 # gprof is a bit different on FreeBSD, disable
  fi

  TEST_REGRESS=test_regress
  if [ "$CI_RELOC" == 1 ]; then
    # Testing that the installation is relocatable.
    "$MAKE" install
    mkdir -p "$RELOC_DIR"
    mv "$INSTALL_DIR" "$RELOC_DIR/relocated-install"
    export VERILATOR_ROOT="$RELOC_DIR/relocated-install/share/verilator"
    TEST_REGRESS="$RELOC_DIR/test_regress"
    mv test_regress "$TEST_REGRESS"
    NODIST="$RELOC_DIR/nodist"
    mv nodist "$NODIST"
    # Feeling brave?
    find . -delete
    ls -la .
  fi

  # Run the specified test
  ccache -z
  case $TESTS in
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
    *)
      fatal "Unknown test: $TESTS"
      ;;
  esac

  # To see load average (1 minute, 5 minute, 15 minute)
  uptime
  # 22.04: ccache -s -v
  ccache -s

else
  ##############################################################################
  # Unknown build stage
  fatal "Unknown build stage: '$CI_BUILD_STAGE_NAME'"
fi
