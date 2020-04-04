# DESCRIPTION: Dockerfile for image to run Verilator inside
#
# Copyright 2020 by Stefan Wallentowitz. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

FROM ubuntu:18.04

RUN apt-get update \
    && apt-get install --no-install-recommends -y \
                        autoconf=2.69-11 \
                        bc=1.07.1-2 \
                        bison=2:3.0.4.dfsg-1build1 \
                        build-essential=12.4ubuntu1 \
                        ca-certificates=20180409 \
                        flex=2.6.4-6 \
                        git=1:2.17.1-1ubuntu0.5 \
                        libfl-dev=2.6.4-6 \
                        perl=5.26.1-6ubuntu0.3 \
                        python3=3.6.7-1~18.04 \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

ARG REPO=https://github.com/verilator/verilator
ARG SOURCE_COMMIT=master

WORKDIR /tmp

# Add an exception for the linter, we want to cd here in one layer
# to reduce the number of layers (and thereby size).
# hadolint ignore=DL3003
RUN git clone "${REPO}" verilator && \
    cd verilator && \
    git checkout "${SOURCE_COMMIT}" && \
    autoconf && \
    ./configure && \
    make -j "$(nproc)" && \
    make install && \
    cd .. && \
    rm -r verilator

COPY verilator-wrap.sh /usr/local/bin/verilator-wrap.sh

WORKDIR /work

ENTRYPOINT [ "/usr/local/bin/verilator-wrap.sh" ]
