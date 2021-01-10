#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI ccache maintenance
#
# Copyright 2020 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# This script is run in 'before_script', once ccache has been set up.
################################################################################

set -e
set -x

# Show version
ccache --version

# Flush ccache if requested in commit message
COMMIT="${CI_PULL_REQUEST_SHA:-$CI_COMMIT}"
if git log --format=%B -n 1 "$COMMIT" | grep -q -i '\[CI\s\+ccache\s\+clear\]'; then
  echo "Flushing ccache due to commit message"
  ccache -C
fi

# Dump stats, then zero stats
ccache -s -z
