#!/bin/bash
######################################################################
# DESCRIPTION: Fuzzer setup to be run as root
#
# Copyright 2019-2019 by Eric Rippey. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
######################################################################

# This is the portion of the fuzzer setup that must be run as root.
# Note that this assumes a Debian-like distribution.

set -e

# Get dependencies
apt-get install afl mdm
apt-get build-dep verilator

# Run a couple pieces of setup which should speed up the fuzzer
echo core >/proc/sys/kernel/core_pattern

cd /sys/devices/system/cpu
echo performance | tee cpu*/cpufreq/scaling_governor
