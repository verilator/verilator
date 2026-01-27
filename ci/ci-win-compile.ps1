# DESCRIPTION: Verilator: CI Windows Power Shell - Compile Verilator
#
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
################################################################################

Set-PSDebug -Trace 1

if (-Not (Test-Path $PWD/../.ccache/win_bison.exe)) {
    git clone --depth 1 https://github.com/lexxmark/winflexbison
    cd winflexbison
    mkdir build
    cd build
    cmake .. --install-prefix $PWD/../../../.ccache
    cmake --build . --config Release -j 3
    cmake --install . --prefix $PWD/../../../.ccache
    cd ../..
}

mkdir build
cd build
cmake .. --install-prefix $PWD/../install
cmake --build . --config Release -j 3
cmake --install . --prefix $PWD/../install
