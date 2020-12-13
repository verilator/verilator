#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI main job script
#
# Copyright 2020 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

echo "::group::build's ci-install"
export CI_BUILD_STAGE_NAME=build
bash ci/ci-install.bash
echo "::endgroup"

echo "::group::build's ci-script"
mkdir -p $CCACHE_DIR && bash ci/ci-ccache-maint.bash
bash ci/ci-script.bash
echo "::endgroup"

echo "::group::test's ci-install"
export CI_BUILD_STAGE_NAME=test
bash ci/ci-install.bash
echo "::endgroup"
