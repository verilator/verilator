#!/usr/bin/env bash
# DESCRIPTION: Verilator: Travis CI early platform workaround
#
# Copyright 2020 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# This script runs very early by setting an env variable to $(<this script>)
# This is to work around travis-ci issues
################################################################################

set -e
set -x

if [ "$TRAVIS_OS_NAME" = "freebsd" ]; then
  # Needs bash in bin for non-portable #! in scripts
  sudo ln -s "$(which bash)" /bin/bash
  # Needs tmate for debug mode (the one in pkg is too old, so build from source)
  sudo pkg install -y libevent
  sudo pkg install -y msgpack
  sudo pkg install -y libssh
  git clone https://github.com/tmate-io/tmate.git /tmp/tmate-build
  pushd /tmp/tmate-build
  git checkout 2.4.0
  ./autogen.sh
  ./configure
  make -j$(sysctl -n hw.ncpu)
  sudo make install
  popd
  # Travis debug scripts also require this to be in /usr/bin rather than
  # /usr/local/bin whre the abote puts it
  sudo ln -s "$(which tmate)" /usr/bin/tmate
fi
