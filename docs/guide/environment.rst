.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

Environment
===========

This section describes the environment variables used by Verilator and
associated programs.

.. option:: LD_LIBRARY_PATH

   A generic Linux/OS variable specifying what directories have shared
   object (.so) files.  This path should include SystemC and any other
   shared objects needed at simulation runtime.

.. option:: MAKE

   Names the executable of the make command invoked when using the
   :vlopt:`--build` option.  Some operating systems may require "gmake" to
   this variable to launch GNU make.  If this variable is not specified,
   "make" is used.

.. option:: OBJCACHE

   Optionally specifies a caching or distribution program to place in front
   of all runs of the C++ compiler.  For example, "ccache".  If using
   :command:`distcc` or :command:`icecc`/:command:`icecream`, they would
   generally be run under :command:`ccache`; see the documentation for
   those programs.  If OBJCACHE is not set, and at configure time ccache
   was present, ccache will be used as a default.

.. option:: SYSTEMC

   Deprecated.  Used only if :option:`SYSTEMC_INCLUDE` or
   :option:`SYSTEMC_LIBDIR` is not set.  If set, specifies the directory
   containing the SystemC distribution.  If not specified, it will come
   from a default optionally specified at configure time (before Verilator
   was compiled).

.. option:: SYSTEMC_ARCH

   Deprecated.  Used only if :option:`SYSTEMC_LIBDIR` is not set.
   Specifies the architecture name used by the SystemC kit.  This is the
   part after the dash in the "lib-{...}" directory name created by a
   :command:`make` in the SystemC distribution.  If not set, Verilator will
   try to intuit the proper setting, or use the default optionally
   specified at configure time (before Verilator was compiled).

.. option:: SYSTEMC_CXX_FLAGS

   Specifies additional flags that are required to be passed to GCC when
   building the SystemC model.  System 2.3.0 may need this set to
   "-pthread".

.. option:: SYSTEMC_INCLUDE

   If set, specifies the directory containing the systemc.h header file. If
   not specified, it will come from a default optionally specified at
   configure time (before Verilator was compiled), or computed from
   SYSTEMC/include.

.. option:: SYSTEMC_LIBDIR

   If set, specifies the directory containing the libsystemc.a library. If
   not specified, it will come from a default optionally specified at
   configure time (before Verilator was compiled), or computed from
   SYSTEMC/lib-SYSTEMC_ARCH.

.. option:: VERILATOR_BIN

   If set, specifies an alternative name of the ``verilator`` binary.  May
   be used for debugging and selecting between multiple operating system
   builds.

.. option:: VERILATOR_COVERAGE_BIN

   If set, specifies an alternative name of the ``verilator_coverage``
   binary.  May be used for debugging and selecting between multiple
   operating system builds.

.. option:: VERILATOR_GDB

   If set, the command to run when using the :vlopt:`--gdb` option, such as
   "ddd".  If not specified, it will use "gdb".

.. option:: VERILATOR_ROOT

   Specifies the directory containing the distribution kit.  This is used
   to find the executable, Perl library, and include files.  If not
   specified, it will come from a default optionally specified at configure
   time (before Verilator was compiled).  It should not be specified if
   using a pre-compiled Verilator package as the hard-coded value should be
   correct.  See :ref:`Installation`.
