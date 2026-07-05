#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI build job script
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# Executed in the 'build' stage.
################################################################################

# Destructive to the checkout (reconfigures and rebuilds); never run locally
if [ "$GITHUB_ACTIONS" != "true" ]; then
  echo "ERROR: $(basename "$0") must only be run in GitHub Actions CI" >&2
  exit 1
fi

set -e
set -x

source "$(dirname "$0")/ci-common.bash"

################################################################################
# Parse arguments

OPT_ASAN=0
OPT_CCWARN=0
OPT_GCOV=0
OPT_COMPILER=
OPT_PREFIX=
while [ $# -gt 0 ]; do
  case "$1" in
    --asan) OPT_ASAN=1 ;;
    --ccwarn) OPT_CCWARN=1 ;;
    --compiler)
      [ $# -ge 2 ] || fatal "--compiler requires an argument"
      OPT_COMPILER="$2"
      shift
      ;;
    --gcov) OPT_GCOV=1 ;;
    --prefix)
      [ $# -ge 2 ] || fatal "--prefix requires an argument"
      OPT_PREFIX="$2"
      shift
      ;;
    *) fatal "Unknown option: '$1'" ;;
  esac
  shift
done

[ -n "$OPT_COMPILER" ] || fatal "--compiler is required"
[ -n "$OPT_PREFIX" ] || fatal "--prefix is required"

# Map the compiler name to the executable name configure CXX expects
case "$OPT_COMPILER" in
  clang) CXX=clang++ ;;
  gcc) CXX=g++ ;;
  *) fatal "Unknown compiler: '$OPT_COMPILER'" ;;
esac

################################################################################
# Configure

CONFIGURE_ARGS="--prefix=$OPT_PREFIX --enable-longtests"
if [ "$OPT_CCWARN" = 1 ]; then
  CONFIGURE_ARGS="$CONFIGURE_ARGS --enable-ccwarn"
fi
if [ "$OPT_ASAN" = 1 ]; then
  CONFIGURE_ARGS="$CONFIGURE_ARGS --enable-dev-asan"
  CXX="$CXX -DVL_LEAK_CHECKS"
fi
if [ "$OPT_GCOV" = 1 ]; then
  CONFIGURE_ARGS="$CONFIGURE_ARGS --enable-dev-gcov"
fi
autoconf
./configure $CONFIGURE_ARGS CXX="$CXX"

################################################################################
# Build

ccache -z
BUILD_START=$SECONDS
"$MAKE" -j "$NPROC" -k
ccache -svv
ccache --evict-older-than "$((SECONDS - BUILD_START + 60))s"
ccache -svv
