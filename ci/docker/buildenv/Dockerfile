# DESCRIPTION: Dockerfile for env to build and fully test Verilator
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2020 Stefan Wallentowitz
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

FROM ubuntu:24.04

# Create the user
RUN groupadd verilator \
    && useradd -g verilator -m verilator -s /bin/bash \
    && apt-get update \
    && apt-get install --no-install-recommends -y sudo \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/* \
    && echo verilator ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/verilator \
    && chmod 0440 /etc/sudoers.d/verilator

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
                        help2man \
                        libfl2 \
                        libfl-dev \
                        libclang-rt-18-dev \
                        libjemalloc-dev \
                        libsystemc \
                        libsystemc-dev \
                        numactl \
                        perl \
                        python3 \
                        python3-distro \
                        wget \
                        z3 \
                        zlib1g \
                        zlib1g-dev \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /tmp

COPY wavetools.conf /tmp/wavetools.conf
ARG WGET_EXTRA_ARGS=
RUN . /tmp/wavetools.conf && \
    wget -q ${WGET_EXTRA_ARGS} -O /tmp/wavetools.tar.gz \
    "https://github.com/hudson-trading/wavetools/releases/download/${WAVETOOLS_VERSION}/wavetools-${WAVETOOLS_VERSION}-linux-x86_64.tar.gz" && \
    tar -xzf /tmp/wavetools.tar.gz -C /tmp && \
    cp /tmp/wavetools-${WAVETOOLS_VERSION}-linux-x86_64/wavediff /usr/local/bin/wavediff && \
    rm -rf /tmp/wavetools.tar.gz /tmp/wavetools-* /tmp/wavetools.conf

COPY build.sh /tmp/build.sh

ENV VERILATOR_AUTHOR_SITE=1

USER verilator

WORKDIR /work

ENTRYPOINT [ "/tmp/build.sh" ]
