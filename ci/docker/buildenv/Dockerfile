# DESCRIPTION: Dockerfile for env to build and fully test Verilator
#
# Copyright 2020 by Stefan Wallentowitz. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

FROM ubuntu:18.04

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive \
       apt-get install --no-install-recommends -y \
                        autoconf=2.69-11 \
                        bc=1.07.1-2 \
                        bison=2:3.0.4.dfsg-1build1 \
                        build-essential=12.4ubuntu1 \
                        ca-certificates=20180409 \
                        cmake=3.10.2-1ubuntu2.18.04.1 \
                        flex=2.6.4-6 \
                        gdb=8.1-0ubuntu3.2 \
                        gcc-6=6.5.0-2ubuntu1~18.04 \
                        gcc-5=5.5.0-12ubuntu1 \
                        gcc-4.8=4.8.5-4ubuntu8 \
                        git=1:2.17.1-1ubuntu0.5 \
                        gtkwave=3.3.86-1 \
                        g++-6=6.5.0-2ubuntu1~18.04 \
                        g++-5=5.5.0-12ubuntu1 \
                        g++-4.8=4.8.5-4ubuntu8 \
                        libfl2=2.6.4-6 \
                        libfl-dev=2.6.4-6 \
                        numactl=2.0.11-2.1ubuntu0.1 \
                        perl=5.26.1-6ubuntu0.3 \
                        python3=3.6.7-1~18.04 \
                        wget=1.19.4-1ubuntu2.2 \
                        zlibc=0.9k-4.3 \
                        zlib1g=1:1.2.11.dfsg-0ubuntu2 \
                        zlib1g-dev=1:1.2.11.dfsg-0ubuntu2 \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /tmp

COPY build-systemc.sh /tmp/
RUN ./build-systemc.sh

RUN cpan install -fi Unix::Processors Parallel::Forker Bit::Vector

RUN git clone https://github.com/veripool/vcddiff.git && \
    make -C vcddiff && \
    cp -p vcddiff/vcddiff /usr/local/bin/vcddiff && \
    rm -rf vcddiff

COPY build.sh /tmp/build.sh

ENV VERILATOR_AUTHOR_SITE=1

ENTRYPOINT [ "/tmp/build.sh" ]
