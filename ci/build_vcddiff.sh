#!/bin/bash
# DESCRIPTION: Verilator: Build script for vcddiff
#
# Copyright 2019 by Todd Strader. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
set -e

# NB: it would be better to add this via a PPA

TMP_DIR=$(mktemp -d)

git -C "${TMP_DIR}" clone https://github.com/veripool/vcddiff
VCDDIFF_DIR=${TMP_DIR}/vcddiff
git -C "${VCDDIFF_DIR}" checkout 5112f88b7ba8818dce9dfb72619e64a1fc19542c
make -C "${VCDDIFF_DIR}"
sudo cp "${VCDDIFF_DIR}/vcddiff" /usr/local/bin
