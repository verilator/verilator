# DESCRIPTION: Dockerfile for image to run Verilator inside
#
# Copyright 2020 by Stefan Wallentowitz. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

FROM ubuntu:20.04

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive \
    && apt-get install --no-install-recommends -y \
                        autoconf \
                        bc \
                        bison \
                        build-essential \
                        ca-certificates \
                        ccache \
                        flex \
                        git \
                        libfl-dev \
                        libgoogle-perftools-dev \
                        perl \
                        python3 \
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
