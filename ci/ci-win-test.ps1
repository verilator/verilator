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

# UVM smoke test: verilate and run the full pre-merged UVM package, the same
# package used by test_regress's t_uvm_hello_all_v2020_3_2_nodpi (the Linux
# regression runs the t_uvm_hello_all_* family). --binary's make flow needs a
# POSIX toolchain (sh, make, g++); the runner image ships a bare MSYS2 at
# C:\msys64, into which the needed packages are installed here.
cd ../../../test_regress
# MSYS2's documented update flow: a -Syu pass may stop after upgrading
# pacman itself and expects a re-run; run it twice, then install packages.
& C:\msys64\usr\bin\pacman.exe -Syu --noconfirm
& C:\msys64\usr\bin\pacman.exe -Syu --noconfirm
& C:\msys64\usr\bin\pacman.exe -S --needed --noconfirm make python mingw-w64-ucrt-x86_64-gcc
if ($LASTEXITCODE -ne 0) { exit 1 }
$Env:MSYSTEM = "UCRT64"
$Env:UVM_T = "$PWD/t"
$Env:UVM_ROOT = "$PWD/../install"
$Env:UVM_J = "$NPROC"
& C:\msys64\usr\bin\bash.exe -lc @'
set -e
T="$(cygpath "$UVM_T")"
ROOT="$(cygpath -m "$UVM_ROOT")"
cd "$T"
export MAKEFLAGS="CXX=g++ LINK=g++ AR=ar PYTHON3=python"
"$ROOT/bin/verilator_bin.exe" --binary -j "$UVM_J" -CFLAGS -O0 -CFLAGS -DVL_TIME_CONTEXT --timing -Wno-fatal --top-module t +incdir+uvm uvm/uvm_pkg_all_v2020_3_2_nodpi.svh t_uvm_hello.v -Mdir obj_uvm
out="$(./obj_uvm/Vt.exe +UVM_NO_RELNOTES < /dev/null 2>&1)"
echo "$out"
echo "$out" | grep -q "UVM TEST PASSED"
# The report summary prints e.g. "UVM_ERROR :    0"; the count may be wider.
if echo "$out" | grep -Eq "UVM_(ERROR|FATAL)[[:space:]]*:[[:space:]]*[1-9]"; then exit 1; fi
rm -rf obj_uvm
'@
if ($LASTEXITCODE -ne 0) { exit 1 }
