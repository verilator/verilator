# DESCRIPTION: Dockerfile for env to build and fully test Verilator
#
# Copyright 2020 by Stefan Wallentowitz. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

FROM ubuntu:20.04

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive \
       apt-get install --no-install-recommends -y \
                        autoconf \
                        bc \
                        bison \
                        build-essential \
                        ca-certificates \
                        ccache \
                        clang \
                        cmake \
                        flex \
                        gdb \
                        git \
                        gtkwave \
                        libfl2 \
                        libfl-dev \
                        libgoogle-perftools-dev \
                        libsystemc \
                        libsystemc-dev \
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

RUN cpan install -fi Parallel::Forker

RUN git clone https://github.com/veripool/vcddiff.git && \
    make -C vcddiff && \
    cp -p vcddiff/vcddiff /usr/local/bin/vcddiff && \
    rm -rf vcddiff

COPY build.sh /tmp/build.sh

ENV VERILATOR_AUTHOR_SITE=1

WORKDIR /work

ENTRYPOINT [ "/tmp/build.sh" ]
