.. Copyright 2003-2024 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _CMakeInstallation:

******************
CMake Installation
******************

This section discusses how to build and install Verilator using cmake.
Currently cmake is only officially supported for Windows builds (not Linux).

.. _Tools Install:

Quick Install
=============

1. Install Python for your platform from https://www.python.org/downloads/.
2. Install CMake for your platform from https://cmake.org/download/ or build it from source.
3. If the compiler of your choice is MSVC, then install https://visualstudio.microsoft.com/downloads/.
   If the compiler of your choice is Clang, then install https://releases.llvm.org/download.html or build it from source.
4. For flex and bison use https://github.com/lexxmark/winflexbison to build and install.
5. For build on Windows using MSVC set environment variable WIN_FLEX_BISON to install directory.
   For build on Windows/Linux/OS-X using ninja set the environment variable
   FLEX_INCLUDE to the directory containing FlexLexer.h and ensure that flex/bison
   is available within the PATH.

To obtain verilator sources download https://github.com/verilator/verilator/archive/refs/heads/master.zip
or clone https://github.com/verilator/verilator using git :ref:`Obtain Sources`.

To build using MSVC:

::

   cd verilator  # directory containing source files of verilator
   mkdir build
   cmake .. -DCMAKE_BUILD_TYPE=Release --install-prefix $PWD/../install
   cmake --build . --config Release
   cmake --install . --prefix $PWD/../install


To build using ninja:

::

    cd verilator
    mkdir build
    cmake -G Ninja .. -DCMAKE_BUILD_TYPE=Release --install-prefix $PWD/../install -DCMAKE_MAKE_PROGRAM=<path to ninja binary> -DBISON_EXECUTABLE=<path to bison> -DFLEX_EXECUTABLE=<path to flex>
    <path to ninja binary> #execute ninja
    cmake --install . --prefix $PWD/../install


.. _CMake Usage:

Usage
=====

To use Verilator set the environment variable ``VERILATOR_ROOT`` to the
install directory specified in the above build.

Example
=======

::

    cd verilator/examples
    cd cmake_hello_c
    mkdir build
    cd build
    cmake ..  # cmake -G Ninja ..
    cmake --build . --config Release # ninja
    # execute the generated binary
