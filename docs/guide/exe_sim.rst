.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _Simulation Runtime Arguments:

Simulation Runtime Arguments
============================

The following are the arguments that may be passed to a Verilated
executable, provided that executable calls
:code:`VerilatedContext*->commandArgs(argc, argv)`.

All simulation runtime arguments begin with "+verilator", so that the
user's executable may skip over all "+verilator" arguments when parsing its
command line.

Summary:

   .. include:: ../_build/gen/args_verilated.rst


.. option:: +verilator+debug

   Enable simulation runtime debugging.  Equivalent to
   :vlopt:`+verilator+debugi+4 <+verilator+debugi+\<value\>>`.

.. option:: +verilator+debugi+<value>

   Enable simulation runtime debugging at the provided level.

.. option:: +verilator+error+limit+<value>

   Set number of non-fatal errors (e.g. assertion failures) before exiting
   simulation runtime. Also affects number of $stop calls needed before
   exit. Defaults to 1.

.. option:: +verilator+help

   Display help and exit.

.. option:: +verilator+prof+exec+file+<filename>

   When a model was Verilated using :vlopt:`--prof-exec`, sets the
   simulation runtime filename to dump to.  Defaults to
   :file:`profile_exec.dat`.

.. option:: +verilator+prof+exec+start+<value>

   When a model was Verilated using :vlopt:`--prof-exec`, the simulation
   runtime will wait until $time is at this value (expressed in units of
   the time precision), then start the profiling warmup, then
   capturing. Generally this should be set to some time that is well within
   the normal operation of the simulation, i.e. outside of reset. If 0, the
   dump is disabled. Defaults to 1.

.. option:: +verilator+prof+exec+window+<value>

   When a model was Verilated using :vlopt:`--prof-exec`, after $time
   reaches :vlopt:`+verilator+prof+exec+start+\<value\>`, Verilator will
   warm up the profiling for this number of eval() calls, then will capture
   the profiling of this number of eval() calls.  Defaults to 2, which
   makes sense for a single-clock-domain module where it's typical to want
   to capture one posedge eval() and one negedge eval().

.. option:: +verilator+prof+threads+file+<filename>

   Deprecated. Alias for :vlopt:`+verilator+prof+exec+file+\<filename\>`

.. option:: +verilator+prof+threads+start+<value>

   Deprecated. Alias for :vlopt:`+verilator+prof+exec+start+\<value\>`

.. option:: +verilator+prof+threads+window+<value>

   Deprecated. Alias for :vlopt:`+verilator+prof+exec+window+\<filename\>`

.. option:: +verilator+prof+vlt+file+<filename>

   When a model was Verilated using :vlopt:`--prof-pgo`, sets the
   profile-guided optimization data runtime filename to dump to.  Defaults
   to :file:`profile.vlt`.

.. option:: +verilator+rand+reset+<value>

   When a model was Verilated using :vlopt:`--x-initial unique
   <--x-initial>`, sets the simulation runtime initialization technique.  0
   = Reset to zeros. 1 = Reset to all-ones.  2 = Randomize.  See
   :ref:`Unknown States`.

.. option:: +verilator+seed+<value>

   For $random and :vlopt:`--x-initial unique <--x-initial>`, set the
   simulation runtime random seed value.  If zero or not specified picks a
   value from the system random number generator.

.. option:: +verilator+noassert

   Disable assert checking per runtime argument. This is the same as
   calling :code:`VerilatedContext*->assertOn(false)` in the model.

.. option:: +verilator+V

   Shows the verbose version, including configuration information.

.. option:: +verilator+version

   Displays program version and exits.
