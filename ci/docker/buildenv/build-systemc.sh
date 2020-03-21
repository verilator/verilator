#!/bin/bash -e
# DESCRIPTION: Build SystemC in Ubuntu 18.04 with  different g++/gcc
#
# Copyright 2020 by Stefan Wallentowitz. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

build_variant () {
    version=$($1 --version | grep gcc | awk '{print $4}')
    mkdir "/usr/local/systemc-2.3.3-gcc$version"
    mkdir build
    cd build
    ../configure --prefix="/usr/local/systemc-2.3.3-gcc$version" CC="$1" CXX="$2" LD="$2"
    make -j
    make install
    cd ..
    rm -r build
}

wget https://www.accellera.org/images/downloads/standards/systemc/systemc-2.3.3.tar.gz
tar -xzf systemc-2.3.3.tar.gz
cd systemc-2.3.3
build_variant gcc g++
build_variant gcc-6 g++-6
build_variant gcc-5 g++-5
build_variant gcc-4.8 g++-4.8
cd ..
rm -r systemc-2.3.3*
