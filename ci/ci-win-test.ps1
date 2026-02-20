# DESCRIPTION: Verilator: CI Windows Power Shell - Verilate a test
#
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
################################################################################


Set-PSDebug -Trace 1

cd install
$Env:VERILATOR_ROOT=$PWD
cd examples/cmake_tracing_c
mkdir build
cd build
cmake ..
cmake --build . --config Release -j 3

# TODO put this back in, see issue# 5163
# Release/example.exe

cd ..
Remove-Item -path build -recurse
