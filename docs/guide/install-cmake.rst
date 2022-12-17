.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _Installation:

************
Installation
************

This section discusses how to install Verilator using cmake.

.. _Tools Install:

Quick Install
=============

Install Python for your platform from https://www.python.org/downloads/
Install CMake for your platform from https://cmake.org/download/ or build it from source
If the compiler of your choice is MSVC then install https://visualstudio.microsoft.com/downloads/
If the compiler of your choice is Clang then install https://releases.llvm.org/download.html or build it from source
For flex and bison use https://github.com/lexxmark/winflexbison to build and install
For build on windows using msvc set environment variable WIN_FLEX_BISON to install directory
For build on windows/linux/osx using ninja set environment variable FLEX_INCLUDE to directory
containing FlexLexer.h and ensure flex/bison is available on the path

To obtain verilator sources download https://github.com/verilator/verilator/archive/refs/heads/master.zip
or clone https://github.com/verilator/verilator using git

To build using msvc

::

   cd verilator # directory containing source files of verilator
   mkdir build
   cmake .. -DCMAKE_BUILD_TYPE=Release --install-prefix $PWD/../install
   cmake --build . --config Release
   cmake --install . --prefix $PWD/../install


To build using ninja

::

    cd verilator
    mkdir build
    cmake -G Ninja .. -DCMAKE_BUILD_TYPE=Release --install-prefix $PWD/../install -DCMAKE_MAKE_PROGRAM=<path to ninja binary> -DBISON_EXECUTABLE=<path to bison> -DFLEX_EXECUTABLE=<path to flex>
    <path to ninja binary> #execute ninja
    cmake --install . --prefix $PWD/../install

.. _Detailed Build Instructions:

Usage
=====

To use verilator set the environment variable ``VERILATOR_ROOT`` to install directory
of the above build

Example
=======

::

    cd verilator/examples
    cd cmake_hello_c
    mkdir build
    cd build
    cmake .. # cmake -G Ninja ..
    cmake --build . --config Release # ninja
    # execute the generated binary

Install GTKWave
^^^^^^^^^^^^^^^

To make use of Verilator FST tracing you will want `GTKwave
<http://gtkwave.sourceforge.net/>`__ installed, however this is not
required at Verilator build time.


Obtain Sources
--------------

Get the sources from the git repository: (You need to do this only once,
ever.)

::

   git clone https://github.com/verilator/verilator   # Only first time
   ## Note the URL above is not a page you can see with a browser; it's for git only

Enter the checkout and determine what version/branch to use:

::

   cd verilator
   git pull        # Make sure we're up-to-date
   git tag         # See what versions exist
   #git checkout master      # Use development branch (e.g. recent bug fix)
   #git checkout stable      # Use most recent release
   #git checkout v{version}  # Switch to specified release version
