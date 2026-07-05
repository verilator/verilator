# DESCRIPTION: Verilator: CI common definitions, sourced by the stage scripts
#
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# Common definitions sourced by the CI stage scripts; not executed directly.
################################################################################

fatal() {
  echo "ERROR: $(basename "$0"): $1" >&2; exit 1;
}

case "$(uname -s)" in
  Linux)
    HOST_OS=linux
    MAKE=make
    NPROC=$(nproc)
    # Distro id/version; subshell keeps os-release out of our namespace
    if [ -r /etc/os-release ]; then
      DISTRO_ID=$(. /etc/os-release; echo "$ID")
      DISTRO_VERSION=$(. /etc/os-release; echo "$VERSION_ID")
    fi
    ;;
  Darwin)
    HOST_OS=macOS
    MAKE=make
    NPROC=$(sysctl -n hw.logicalcpu)
    # Disable ccache, doesn't always work in GitHub Actions
    export OBJCACHE=
    ;;
  *)
    fatal "Unknown host OS: '$(uname -s)'"
    ;;
esac

export MAKE
