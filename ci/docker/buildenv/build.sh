#!/bin/bash -e
# DESCRIPTION: Build Verilator (inside container)
#
# Copyright 2020 by Stefan Wallentowitz. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

: "${REPO:=https://github.com/verilator/verilator}"
: "${REV:=master}"
: "${CC:=gcc}"
: "${CXX:=g++}"

SRCS=$PWD/verilator

git clone "$REPO" "$SRCS"
cd "$SRCS"
git checkout "$REV"
autoconf
./configure --enable-longtests
make -j $(nproc)
if [ "${1:-''}" == "test" ]; then
    make test
fi
