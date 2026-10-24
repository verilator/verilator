# DESCRIPTION: Verilator: CI Windows Power Shell - Verilate a test
#
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
################################################################################


Set-PSDebug -Trace 1

$NPROC = $env:NUMBER_OF_PROCESSORS

cd install
$Env:VERILATOR_ROOT=$PWD
cd examples/cmake_tracing_c
mkdir build
cd build
# /Od skips optimization; this only checks the example verilates and builds, so
# an optimized binary is not needed (see ci-win-compile.ps1).
# /MT statically links the CRT so the binary does not depend on the
# msvcp140.dll installed on the machine (root cause of issue# 5163).
cmake .. "-DCMAKE_CXX_FLAGS_RELEASE=/Od /DNDEBUG /MT"
cmake --build . --config Release -j $NPROC
Release/example.exe

cd ..
Remove-Item -path build -recurse

cd ../cmake_hello_c
mkdir build
cd build
# /Od skips optimization; this only checks the example verilates and builds, so
# an optimized binary is not needed (see ci-win-compile.ps1).
# /MT statically links the CRT so the binary does not depend on the
# msvcp140.dll installed on the machine (root cause of issue# 5163).
cmake .. "-DCMAKE_CXX_FLAGS_RELEASE=/Od /DNDEBUG /MT"
cmake --build . --config Release -j $NPROC
Release/example.exe

cd ..
Remove-Item -path build -recurse
