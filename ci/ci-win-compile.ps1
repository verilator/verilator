# DESCRIPTION: Verilator: CI Windows Power Shell - Compile Verilator
#
# SPDX-FileCopyrightText: 2024 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
################################################################################

Set-PSDebug -Trace 1

$NPROC = $env:NUMBER_OF_PROCESSORS

# Absolute path for the win_flex_bison install; CMake reads this from the environment
$env:WIN_FLEX_BISON = "$(Resolve-Path ..)/win_flex_bison"

if (-Not (Test-Path $env:WIN_FLEX_BISON/win_bison.exe)) {
    git clone --depth 1 https://github.com/lexxmark/winflexbison
    cd winflexbison
    mkdir build
    cd build
    cmake .. --install-prefix $env:WIN_FLEX_BISON
    cmake --build . --config Release -j $NPROC
    cmake --install . --prefix $env:WIN_FLEX_BISON
    cd ../..
}

# Enter the MSVC developer shell so cl/link are on PATH for the Ninja generator
$VsPath = & "${env:ProgramFiles(x86)}/Microsoft Visual Studio/Installer/vswhere.exe" -latest -products * -property installationPath
Import-Module "$VsPath/Common7/Tools/Microsoft.VisualStudio.DevShell.dll"
Enter-VsDevShell -VsInstallPath $VsPath -SkipAutomaticLocation -DevCmdArguments "-arch=x64 -host_arch=x64"

mkdir build
cd build
# Ninja saturates all cores; the MSBuild generator only parallelizes across
# projects and Verilator is a single target, so it compiles serially. /Od skips
# optimization: this job only checks that Verilator builds and can verilate an
# example, so an optimized binary is not needed and the codegen time dominates.
# Turn warnings that were fixed in the recent Windows cleanups into errors, so they
# cannot creep back in: C4715 (falling off the end of a non-void function),
# C4806/C4805 (bool/integer masking).  Set through CXXFLAGS so that the flags CMake
# already passes are kept; replacing CMAKE_CXX_FLAGS outright loses /EHsc and makes
# the STL headers warn with C4530.
$env:CXXFLAGS = "/we4715 /we4806 /we4805"
cmake .. -G Ninja -DCMAKE_BUILD_TYPE=Release --install-prefix $PWD/../install "-DCMAKE_CXX_FLAGS_RELEASE=/Od /DNDEBUG"
cmake --build .
cmake --install . --prefix $PWD/../install

# verilated_dpi.cpp is not part of any CMake target, so nothing above compiles it.
# Whether svdpi.h declares the DPI functions as imports or exports depends on the
# macros set in that file, and getting it wrong is inconsistent dll linkage: only
# warnings at build time, and a link failure once a model uses DPI.  Compile it
# here with that as an error so CI catches it (see issue #9104).
$InstallDir = "$PWD/../install"
& cl /nologo /c /EHsc /W3 /we4273 `
    /Fo:"$env:TEMP\verilated_dpi.obj" `
    /I "$InstallDir/include" /I "$InstallDir/include/vltstd" `
    "$InstallDir/include/verilated_dpi.cpp"
if ($LASTEXITCODE -ne 0) { exit 1 }
