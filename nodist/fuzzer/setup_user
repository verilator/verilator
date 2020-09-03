#!/bin/bash
######################################################################
# DESCRIPTION: Fuzzer setup to be run as a normal user
#
# Copyright 2019-2019 by Eric Rippey. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
######################################################################

# This is the portion of the setup for fuzzing that does not require root access.

set -e

# Build instrumented version of verilator
pushd ../..
autoconf
AFL_HARDEN=1 CC=afl-gcc CXX=afl-g++ ./configure $(cd ..; pwd)
make clean
make -j $(ncpus)
popd

# Create a listing of likely snippets for the fuzzer to use.
# Not essential, but makes things likely to be found faster.
./generate_dictionary

# Set up input directory
mkdir in1
echo "module m; initial \$display(\"Hello world!\n\"); endmodule" > in1/1.v

# Compile wrapper program
AFL_HARDEN=1 CXX=afl-g++ make wrapper
