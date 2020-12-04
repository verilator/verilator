#!/usr/bin/env bash
# DESCRIPTION: Verilator: Travis CI ccache sizer
#
# Copyright 2020 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# This script computes the size of the ccache to be used for a job. We want the
# ccache to be just big enough to be able to hold a whole build so a re-build
# of the same does not miss in the cache due to capacity, but we don't want the
# ccache too big as pulling it down from the network takes time, and it is
# unlikely objects from much earlier builds would be useful.
################################################################################

fatal() {
  echo "ERROR: $(basename "$0"): $1" >&2; exit 1;
}

if [ "$TRAVIS_BUILD_STAGE_NAME" = "build" ]; then
  if [ "$COVERAGE" == 1 ]; then
    echo "1024M"
  else
    echo "768M"
  fi
elif [ "$TRAVIS_BUILD_STAGE_NAME" = "test" ]; then
  if [[ $TESTS == coverage-* ]]; then
    echo "1536M"
  else
    echo "256M"
  fi
else
  fatal "Unknown build stage: '$TRAVIS_BUILD_STAGE_NAME'"
fi
