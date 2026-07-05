#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI dependency install script
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# This script runs in the 'install' phase of all jobs, in all stages. We try to
# minimize the time spent in this by selectively installing only the components
# required by the particular build stage.
################################################################################

# Installs system packages with sudo; never run locally
if [ "$GITHUB_ACTIONS" != "true" ]; then
  echo "ERROR: $(basename "$0") must only be run in GitHub Actions CI" >&2
  exit 1
fi

set -e
set -x

cd $(dirname "$0")/..

source "$(dirname "$0")/ci-common.bash"

################################################################################
# Parse arguments

# Which stage to install dependencies for: 'build' or 'test'
STAGE="$1"

################################################################################
# Install dependencies

# Avoid occasional cpan failures "Issued certificate has expired."
export PERL_LWP_SSL_VERIFY_HOSTNAME=0
echo "check_certificate = off" >> ~/.wgetrc

if [ "$HOST_OS" = "linux" ]; then
  # Avoid slow "processing triggers for man db"
  echo "path-exclude /usr/share/doc/*"  | sudo tee -a /etc/dpkg/dpkg.cfg.d/01_nodoc
  echo "path-exclude /usr/share/man/*"  | sudo tee -a /etc/dpkg/dpkg.cfg.d/01_nodoc
  echo "path-exclude /usr/share/info/*" | sudo tee -a /etc/dpkg/dpkg.cfg.d/01_nodoc
fi

install-wavediff() {
  source ci/docker/buildenv/wavetools.conf
  local _base_url="https://github.com/hudson-trading/wavetools/releases/download/${WAVETOOLS_VERSION}"
  local _platform
  if [ "$HOST_OS" = "linux" ]; then
    _platform="linux-x86_64"
  elif [ "$HOST_OS" = "macOS" ]; then
    _platform="macos-arm64"
  else
    echo "WARNING: No wavetools binary available for HOST_OS=$HOST_OS, skipping"
    return 0
  fi
  local _tmpdir
  _tmpdir=$(mktemp -d)
  local _archive="wavetools-${WAVETOOLS_VERSION}-${_platform}"
  wget -q -O "${_tmpdir}/${_archive}.tar.gz" "${_base_url}/${_archive}.tar.gz"
  tar -xzf "${_tmpdir}/${_archive}.tar.gz" -C "${_tmpdir}"
  sudo cp "${_tmpdir}/${_archive}/wavediff" /usr/local/bin/wavediff
  rm -rf "${_tmpdir}"
}

if [ "$STAGE" = "build" ]; then
  ##############################################################################
  # Dependencies of jobs in the 'build' stage, i.e.: packages required to
  # build Verilator

  if [ "$HOST_OS" = "linux" ]; then
    if [ "$DISTRO_ID" = "ubuntu" ]; then
      PACKAGES=(
        bear
        ccache
        help2man
        libfl-dev
        libsystemc-dev
        mold
      )
      # libunwind conflict on 22.04, can live without libjemalloc there
      if [ "$DISTRO_VERSION" != "22.04" ]; then
        PACKAGES+=(libjemalloc-dev)
      fi
      sudo apt-get update ||
      sudo apt-get update
      sudo apt-get install --yes "${PACKAGES[@]}" ||
      sudo apt-get install --yes "${PACKAGES[@]}"
    fi
  elif [ "$HOST_OS" = "macOS" ]; then
    PACKAGES=(
      autoconf
      bison
      ccache
      flex
      gperftools
      help2man
      perl
    )
    brew update ||
    brew update
    brew install "${PACKAGES[@]}" ||
    brew install "${PACKAGES[@]}"
  else
    fatal "Unknown HOST_OS: '$HOST_OS'"
  fi
elif [ "$STAGE" = "test" ]; then
  ##############################################################################
  # Dependencies of jobs in the 'test' stage, i.e.: packages required to
  # run the tests

  if [ "$HOST_OS" = "linux" ]; then
    if [ "$DISTRO_ID" = "ubuntu" ]; then
      PACKAGES=(
        ccache
        gdb
        jq
        lcov
        libfl-dev
        libsystemc-dev
        mold
        python3-clang
        z3
      )
      sudo apt-get update ||
      sudo apt-get update
      sudo apt-get install --yes "${PACKAGES[@]}" ||
      sudo apt-get install --yes "${PACKAGES[@]}"
    fi
  elif [ "$HOST_OS" = "macOS" ]; then
    PACKAGES=(
      ccache
      jq
      perl
      z3
    )
    brew update ||
    brew update
    brew install "${PACKAGES[@]}" ||
    brew install "${PACKAGES[@]}"
  else
    fatal "Unknown HOST_OS: '$HOST_OS'"
  fi
  # Common installs
  install-wavediff
  # Workaround -fsanitize=address crash
  sudo sysctl -w vm.mmap_rnd_bits=28
else
  ##############################################################################
  # Unknown build stage
  fatal "Unknown stage '$STAGE' (expected 'build' or 'test')"
fi

# Report where the tools we may have installed live (ok if some are missing)
set +x
echo "Tools:"
for bin in autoconf bear bison ccache flex gdb help2man jq lcov mold perl wavediff z3; do
  echo -n "  $bin: "
  which "$bin" || echo "Not found"
done
