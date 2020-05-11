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
                        autoconf \
                        bc \
                        bison \
                        build-essential \
                        ca-certificates \
                        cmake \
                        flex \
                        gdb \
                        gcc-6 \
                        gcc-5 \
                        gcc-4.8 \
                        git \
                        gtkwave \
                        g++-6 \
                        g++-5 \
                        g++-4.8 \
                        libfl2 \
                        libfl-dev \
                        numactl \
                        perl \
                        python3 \
                        wget \
                        zlibc \
                        zlib1g \
                        zlib1g-dev \
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
