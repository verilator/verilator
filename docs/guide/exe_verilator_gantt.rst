.. Copyright 2003-2021 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

verilator_gantt
===============

Verilator_gantt creates a visual representation to help analyze Verilator
multithreaded simulation performance, by showing when each macro-task
starts and ends, and showing when each thread is busy or idle.

For an overview of use of verilator_gantt, see :ref:`Profiling`.

Gantt Chart Contents
--------------------

The generated Gantt chart has time on the X-axis. Times shown are to the
scale printed, i.e. a certain about of time for each character width.  The
Y-axis shows threads, each thread's execution is shown on one line.  That
line shows "[" at the position in time when it executes.

Following the "[" is the CPU number the task executed on, followed by zero
or more "-" to make the width of the characters match the scaled execution
time, followed by a "]".  If the scale is too small, the CPU number and
mtask number will not be printed.  If the scale is very small, a "&"
indicates multiple mtasks started at that time position.

Also creates a value change dump (VCD) format dump file which may be viewed
in a waveform viewer (e.g. C<GTKWave>).  See below.

.. figure:: figures/fig_gantt_min.png

   Example verilator_gantt output, as viewed with GTKWave.


Gantt Chart VCD Signals
-----------------------

In waveforms there are the following signals. In GTKWave, using a data
format of "decimal" will remove the leading zeros and make the traces
easier to read.

evals
  Increments each time when eval_step was measured to be active.  This
  allow visualization of how much time eval_step was active.

eval_loop
  Increments each time when the evaluation loop within eval_step was
  measured to be active.  For best performance there is only a single
  evaluation loop within each eval_step call, that is the eval_loop
  waveform looks identical to the evals waveform.

measured_parallelism
  The number of mtasks active at this time, for best performance this will
  match the thread count. In GTKWave, use a data format of "analog step" to
  view this signal.

predicted_parallelism
  The number of mtasks Verilator predicted would be active at this time,
  for best performance this will match the thread count. In GTKWave, use a
  data format of "analog step" to view this signal.

cpu#_thread
  For the given CPU number, the thread number measured to be executing.

mtask#_cpu
  For the given mtask id, the CPU it was measured to execute on.

thread#_mtask
  For the given thread number, the mtask id it was executing.

predicted_thread#_mtask
  For the given thread number, the mtask id Verilator predicted would be
  executing.


verilator_gantt Arguments
-------------------------

.. program:: verilator_gantt

.. option:: <filename>

The filename to read data from, defaults to "profile_threads.dat".

.. option:: --help

Displays a help summary, the program version, and exits.

.. option:: --scale <n>

Sets the number of time units per character on the X-axis of the generated
Gantt chart.  (On x86, time units are rdtsc ticks.)  Defaults to 0, which
will automatically compute a reasonable scale where no two mtasks need to
fit into same character width's worth of scaled time.

.. option:: --no-vcd

Disables creating a .vcd file.

.. option:: --vcd <filename>

Sets the output filename for vcd dump. Default is "verilator_gantt.vcd".
