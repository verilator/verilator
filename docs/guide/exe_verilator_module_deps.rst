..
   SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
   SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

verilator_module_deps
=====================

Verilator_module_deps scans user C++ sources for C++20 module interface
units and writes the make rules that build them in dependency order. It is
installed privately for the generated makefiles and is normally run by
``make``, not by hand; see :vlopt:`--cxx-modules`.

When C++ modules are built, the generated makefile for a model calls this
program to write a make fragment (``<prefix>__modules.mk``). The fragment
builds the module interface units, their CMIs, and any GCC header units
imported by user sources, and orders the remaining compilation after them.
After each scan it also writes ``<prefix>__modules.json`` and
``<prefix>__modules.dot``, which describe the module and header unit
dependency graph.

The helper scans user sources with the dependency format of the selected
backend. The ``gcc`` backend uses GCC's P1689 output, and the ``clang``
backend uses :command:`clang-scan-deps`. GCC refuses to scan a source that
imports a header unit (``import "header.h";``) until the header unit's CMI
exists, so the helper builds any missing header unit CMIs before scanning.
The generated make rules still rebuild those CMIs when the header changes.

The helper also writes ``<prefix>__modules.stamp``, which records the backend,
the compiler and its version, ``CXXFLAGS``, ``CPPFLAGS``, ``OPT_FAST``, the
include search paths, and the path and modification time of the ``std``
module when it exists.  The stamp is only rewritten when its contents change,
and the generated module objects and CMIs depend on it.  Changing any recorded
build input therefore rebuilds the module CMIs, PCMs, header unit CMIs, and
module objects without rebuilding them on an unchanged build.

verilator_module_deps Arguments
-------------------------------

.. program:: verilator_module_deps

.. option:: --backend <gcc|clang>

   Dependency scanning backend.  The generated makefile passes
   ``VK_MODULE_BACKEND``, which is detected from the C++ compiler in use.
   If the detection is incorrect, set ``VK_MODULE_BACKEND=gcc`` or
   ``VK_MODULE_BACKEND=clang`` explicitly on the make command line.

.. option:: --cppflags <flags>

   Preprocessor flags to pass when scanning and building module interfaces.
   The generated makefile passes ``$(CPPFLAGS)``.

.. option:: --cxx <compiler>

   C++ compiler used for scanning and for the rules written to the output
   fragment.

.. option:: --cxxflags <flags>

   C++ compiler flags to pass when scanning and building module interfaces.
   The generated makefile passes ``$(CXXFLAGS)``.

.. option:: --dot <filename>

   DOT dependency graph to write.  Module import edges have the label
   ``module``.  Edges from a module to a header unit CMI, and from a header
   unit CMI to its header source, have the label ``header``.

.. option:: --json <filename>

   JSON dependency graph to write.  The top-level keys are ``backend``,
   ``modules``, and ``edges``.  Each module entry has ``name``, ``source``,
   ``object``, ``cmi``, ``pcm``, ``provides``, and ``requires``.  Each edge
   has ``from``, ``to``, and ``kind``; ``kind`` is ``module`` or ``header``.

.. option:: --objdir <directory>

   Directory for generated dependency files and CMIs.  Defaults to the
   current directory.

.. option:: --opt-fast <flags>

   Optimization flags for the fast build.  The generated makefile passes
   ``$(OPT_FAST)``.

.. option:: --output <filename>

   Make fragment to write.

.. option:: --source <filename>

   C++ source file to scan.  May be repeated.

.. option:: --stamp <filename>

   Build input stamp to write.  The file is only rewritten when its
   contents change.
