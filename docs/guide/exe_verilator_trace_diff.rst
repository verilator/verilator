..
   SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
   SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

verilator_trace_diff
====================

Verilator_trace_diff compares two VCD or FST traces and reports the first
signal whose value differs. Signals are matched by their full hierarchical
names, and timestamps are normalized using each trace's ``$timescale``.

FST input requires :command:`fst2vcd` from GTKWave. The trace is converted to
a temporary VCD, which is removed when the comparison finishes.

The exit status is 0 when the traces match, 1 when the first difference is
found, and 2 for argument or trace format errors.


verilator_trace_diff Example Usage
----------------------------------

.. code-block:: bash

   verilator_trace_diff --help

   verilator_trace_diff trace1.vcd trace2.vcd

   verilator_trace_diff --clock top.clk trace1.vcd trace2.fst


verilator_trace_diff Arguments
------------------------------

.. program:: verilator_trace_diff

.. option:: <trace1>

   First VCD or FST trace to compare.

.. option:: <trace2>

   Second VCD or FST trace to compare.

.. option:: --clock <signal>

   Full hierarchical name of a 1-bit clock signal. When given, the reported
   cycle is the number of rising edges on that clock at or before the time of
   the first difference.

.. option:: --help

   Displays a help summary and exits.
