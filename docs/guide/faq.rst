.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

******************************
FAQ/Frequently Asked Questions
******************************

.. Extra heading level here so sidebar index looks nice

Questions
=========

Can I contribute?
"""""""""""""""""

Please contribute!  Just submit a pull request, or raise an issue to
discuss if looking for something to help on.  For more information see our
contributor agreement.


How widely is Verilator used?
"""""""""""""""""""""""""""""

Verilator is used by many of the largest silicon design companies, large
organizations such as CERN, and even by college student projects.

Verilator is one of the "big 4" simulators, meaning one of the 4 main
SystemVerilog simulators available, namely the closed-source products Synopsys
VCS (tm), Mentor Questa/ModelSim (tm), Cadence
Xcelium/Incisive/NC-Verilog/NC-Sim (tm), and the open-source Verilator.
The three closed-source offerings are often collectively called the "big 3"
simulators.


Does Verilator run under Windows?
"""""""""""""""""""""""""""""""""

Yes, ideally run Ubuntu under Windows Subsystem for Linux (WSL2).
Alternatively use Cygwin, though this tends to be slower and is not
regularly tested.  Verilated output also compiles under Microsoft Visual
C++, but this is also not regularly tested.


Can you provide binaries?
"""""""""""""""""""""""""

You can install Verilator via the system package manager (apt, yum, etc.)
on many Linux distributions, including Debian, Ubuntu, SuSE, Red Hat, and
others.  These packages are provided by the Linux distributions and
generally will lag the version of the mainline Verilator repository.  If no
binary package is available for your distribution, how about you set one
up?


How can it be faster than (name-a-big-3-closed-source-simulator)?
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

Generally, the implied part of the question is "... with all of the
manpower they can put into developing it."

Most simulators have to be compliant with the complete IEEE 1364 (Verilog)
and IEEE 1800 (SystemVerilog) standards, meaning they have to be event
driven.  This prevents them from being able to reorder blocks and make
netlist-style optimizations, which are where most of the gains come from.

You should not be scared by non-compliance.  Your synthesis tool isn't
compliant with the whole standard to start with, so your simulator need not
be either.  Verilator is closer to the synthesis interpretation, so this is
a good thing for getting working silicon.


Will Verilator output remain under my own license/copyright?
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

Your SystemVerilog, VPI/DPI, or main() C++ code remains under your own license.

It's just like how using GCC on your programs does not change the copyright
of your program; this is why Verilator uses the "GNU **Lesser** Public
License Version 3" instead of the more typical "GNU Public License".  See
the licenses for details.

Some examples:

* Any SystemVerilog or other input fed into Verilator remain your own.

* Any of your VPI/DPI C++ routines that Verilator calls remain your own.

* Any of your main() C++ code that calls into Verilator remain your own.

* If you change Verilator itself, for example changing or adding a file
  under the src/ directory in the repository, you must make the source code
  available under the GNU Lesser Public License.

* If you change a header Verilator provides, for example under include/ in
  the repository, you must make the source code available under the GNU
  Lesser Public License.

You also have the option of using the Perl Artistic License, which again
does not require you to release your Verilog, C++, or generated code. This
license also allows you to modify Verilator for internal use without
distributing the modified version.  But please contribute back to the
community!

Under both license you can offer a commercial product that is based on
Verilator either directly or embedded within.  However under both licenses,
any changes you make to Verilator for such a product must be open sourced.

As is standard with Open Source, contributions back to Verilator will be
placed under the Verilator copyright and LGPL/Artistic license.  Small test
cases will be released into the public domain so they can be used anywhere,
and large tests under the LGPL/Artistic, unless requested otherwise.


Why is running Verilator (to create a model) so slow?
"""""""""""""""""""""""""""""""""""""""""""""""""""""

Verilator may require more memory than the resulting simulator will
require, as Verilator internally creates all of the state of the resulting
generated simulator in order to optimize it.  If it takes more than a few
minutes or so (and you're not using :vlopt:`--debug` since debug mode is
disk bound), see if your machine is paging; most likely you need to run it
on a machine with more memory. Very large designs are known to have topped
64 GB resident set size.  Alternatively, see :ref:`Hierarchical Verilation`.


How do I generate waveforms (traces) in C++?
""""""""""""""""""""""""""""""""""""""""""""

See also the next question for tracing in SystemC mode.

A. Pass the :vlopt:`--trace` option to Verilator, and in your top level C
   code, call ``Verilated::traceEverOn(true)``.  Then you may use
   ``$dumpfile`` and ``$dumpvars`` to enable traces, same as with any
   Verilog simulator. See ``examples/make_tracing_c`` in the distribution.

B. Or, for finer-grained control, or C++ files with multiple Verilated
   modules you may also create the trace purely from C++.  Create a
   VerilatedVcdC object, and in your main loop right after ``eval()`` call
   ``trace_object->dump(contextp->time())`` every time step, and finally
   call ``trace_object->close()``.

   .. code-block:: C++
      :emphasize-lines: 1,5-8,12

      #include "verilated_vcd_c.h"
      ...
      int main(int argc, char** argv, char** env) {
          const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
          ...
          Verilated::traceEverOn(true);
          VerilatedVcdC* tfp = new VerilatedVcdC;
          topp->trace(tfp, 99);  // Trace 99 levels of hierarchy (or see below)
          // tfp->dumpvars(1, "t");  // trace 1 level under "t"
          tfp->open("obj_dir/t_trace_ena_cc/simx.vcd");
          ...
          while (contextp->time() < sim_time && !contextp->gotFinish()) {
              contextp->timeInc(1);
              topp->eval();
              tfp->dump(contextp->time());
          }
          tfp->close();
      }

You also need to compile :file:`verilated_vcd_c.cpp` and add it to your
link, preferably by adding the dependencies in your Makefile's
:code:`$(VK_GLOBAL_OBJS)` link rule.  This is done for you if using the
Verilator :vlopt:`--exe` option.

you can call :code:`trace_object->trace()` on multiple Verilated objects
with the same trace file if you want all data to land in the same output
file.


How do I generate waveforms (traces) in SystemC?
""""""""""""""""""""""""""""""""""""""""""""""""

A. Pass the :vlopt:`--trace` option to Verilator, and in your top level
   :code:`sc_main()`, call :code:`Verilated::traceEverOn(true)`.  Then you
   may use :code:`$dumpfile` and code:`$dumpvars` to enable traces, same as
   with any Verilog simulator, see the non-SystemC example in
   :file:`examples/make_tracing_c`. This will trace only the module
   containing the :code:`$dumpvar`.

B. Or, you may create a trace purely from SystemC, which may trace all
   Verilated designs in the SystemC model. Create a VerilatedVcdSc object
   as you would create a normal SystemC trace file.  For an example, see
   the call to ``VerilatedVcdSc`` in the
   :file:`examples/make_tracing_sc/sc_main.cpp` file of the distribution,
   and below.

C. Alternatively you may use the C++ trace mechanism described in the
   previous question, note the timescale and timeprecision will be
   inherited from your SystemC settings.

   .. code-block:: C++
      :emphasize-lines: 1,5-8

      #include "verilated_vcd_sc.h"
      ...
      int main(int argc, char** argv, char** env) {
          ...
          Verilated::traceEverOn(true);
          VerilatedVcdSc* tfp = new VerilatedVcdSc;
          topp->trace(tfp, 99);  // Trace 99 levels of hierarchy
          tfp->open("obj_dir/t_trace_ena_cc/simx.vcd");
          ...
          sc_start(1);
          ...
          tfp->close();
      }



You also need to compile :file:`verilated_vcd_sc.cpp` and
:file:`verilated_vcd_c.cpp` and add them to your link, preferably by adding
the dependencies in your Makefile's :code:`$(VK_GLOBAL_OBJS)` link rule.
This is done for you if using the Verilator :vlopt:`--exe` option.

You can call :code:`->trace()` on multiple Verilated objects with the same
trace file if you want all data to land in the same output file.

When using SystemC 2.3, the SystemC library must have been built with the
experimental simulation phase callback based tracing disabled. This is
disabled by default when building SystemC with its configure based build
system, but when building SystemC with CMake, you must pass
``-DENABLE_PHASE_CALLBACKS_TRACING=OFF`` to disable this feature.


How do I generate FST waveforms (traces) in C++ or SystemC?
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

FST is a trace file format developed by GTKWave.  Verilator provides basic
FST support.  To dump traces in FST format, add the :vlopt:`--trace-fst`
option to Verilator and either A. use :code:`$dumpfile & $dumpvars` in
Verilog as described in the VCD example above,

Or, in C++ change the include described in the VCD example above:

.. code-block:: C++

      #include "verilated_fst_c.h"
      VerilatedFstC* tfp = new VerilatedFstC;


Or, in SystemC change the include described in the VCD example above:

.. code-block:: C++

      #include "verilated_fst_sc.h"
      VerilatedFstC* tfp = new VerilatedFstSc;


Note that currently supporting both FST and VCD in a single simulation is
impossible, but such requirement should be rare.  You can however ifdef
around the trace format in your C++ main loop, and select VCD or FST at
build time, should you require.


How do I view waveforms (aka dumps or traces)?
""""""""""""""""""""""""""""""""""""""""""""""

Verilator creates standard VCD (Value Change Dump) and FST files.  VCD
files are viewable with the open source GTKWave (recommended) or Dinotrace
(legacy) programs, or any of the many closed-source offerings; FST is
supported only by GTKWave.


How do I speed up writing large waveform (trace) files?
"""""""""""""""""""""""""""""""""""""""""""""""""""""""

A. Instead of calling ``VerilatedVcdC->open`` or ``$dumpvars`` at the
   beginning of time, delay calling it until the time stamp where you want
   tracing to begin.

B. Add the :option:`/*verilator&32;tracing_off*/` metacomment to any very
   low level modules you never want to trace (such as perhaps library
   cells).

C. Use the :vlopt:`--trace-depth` option to limit the depth of tracing, for
   example :vlopt:`--trace-depth 1 <--trace-depth>` to see only the top
   level signals.

D. You can also consider using FST tracing instead of VCD. FST dumps are a
   fraction of the size of the equivalent VCD. FST tracing can be slower
   than VCD tracing, but it might be the only option if the VCD file size
   is prohibitively large.

E. Be sure you write your trace files to a local solid-state drive, instead
   of to a network drive.  Network drives are generally far slower.


Where is the translate_off command?  (How do I ignore a construct?)
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

Translate on/off pragmas are generally a bad idea, as it's easy to have
mismatched pairs, and you can't see what another tool sees by just
preprocessing the code.  Instead, use the preprocessor; Verilator defines
the ``\`VERILATOR`` define for you, so just wrap the code in an ifndef
region:

 .. code-block:: sv
    :emphasize-lines: 1

    `ifndef VERILATOR
       Something_Verilator_Dislikes;
    `endif

Most synthesis tools similarly define SYNTHESIS for you.


Why do I get "unexpected 'do'" or "unexpected 'bit'" errors?
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

The words \ ``do``\ , \ ``bit``\ , \ ``ref``\ , \ ``return``\ , and others
are reserved keywords in SystemVerilog.  Older Verilog code might use these
as identifiers.  You should change your code to not use them to ensure it
works with newer tools.  Alternatively, surround them by the Verilog
2005/SystemVerilog begin_keywords pragma to indicate Verilog 2001 code.

.. code-block:: sv
   :emphasize-lines: 1

   `begin_keywords "1364-2001"
      integer bit; initial bit = 1;
   `end_keywords


If you want the whole design to be parsed as Verilog 2001, see the
:vlopt:`--default-language` option.


How do I prevent my assertions from firing during reset?
""""""""""""""""""""""""""""""""""""""""""""""""""""""""

Call :code:`Verilated::assertOn(false)` before you first call the model,
then turn it back on after reset.  It defaults to true.  When false, all
assertions controlled by :vlopt:`--assert` are disabled.


Why do I get "undefined reference to sc_time_stamp()?
"""""""""""""""""""""""""""""""""""""""""""""""""""""

In Verilator 4.200 and later, using the timeInc function is recommended
instead.  See the :ref:`Connecting to C++` examples.  Some linkers (MSVC++)
still require :code:`sc_time_stamp()` to be defined, either define this
with :code:`double sc_time_stamp() { return 0; }` or compile the Verilated
code with :code:`-CFLAGS -DVL_TIME_CONTEXT`.

Prior to Verilator 4.200, the :code:`sc_time_stamp()` function needs to be
defined in C++ (non SystemC) to return the current simulation time.


Why do I get "undefined reference to \`VL_RAND_RESET_I' or \`Verilated::...'"?
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

You need to link your compiled Verilated code against the
:code:`verilated.cpp` file found in the include directory of the Verilator
kit.  This is one target in the ``$(VK_GLOBAL_OBJS)`` make variable, which
should be part of your Makefile's link rule.  If you use :vlopt:`--exe`,
this is done for you.


Is the PLI supported?
"""""""""""""""""""""

Only somewhat.  More specifically, the common PLI-ish calls $display,
$finish, $stop, $time, $write are converted to C++ equivalents.  You can
also use the "import DPI" SystemVerilog feature to call C code (see the
chapter above).  There is also limited VPI access to public signals.

If you want something more complex, since Verilator emits standard C++
code, you can write your own C++ routines that can access and modify signal
values without needing any PLI interface code, and call it with
$c("{any_c++_statement}").

See the :ref:`Connecting` section.


How do I make a Verilog module that contain a C++ object?
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""

You need to add the object to the structure that Verilator creates, then
use $c to call a method inside your object.  The
:file:`test_regress/t/t_extend_class` files in the distribution show an
example of how to do this.


How do I get faster build times?
""""""""""""""""""""""""""""""""

* When running make, pass the make variable VM_PARALLEL_BUILDS=1 so that
  builds occur in parallel. Note this is now set by default if an output
  file was large enough to be split due to the :vlopt:`--output-split`
  option.

* Verilator emits any infrequently executed "cold" routines into separate
  __Slow.cpp files. This can accelerate compilation as optimization can be
  disabled on these routines. See the OPT_FAST and OPT_SLOW make variables
  and :ref:`Benchmarking & Optimization`.

* Use a recent compiler.  Newer compilers tend to be faster.

* Compile in parallel on many machines and use caching; see the web for the
  ccache, distcc and icecream packages. ccache will skip GCC runs between
  identical source builds, even across different users.  If ccache was
  installed when Verilator was built it is used, or see OBJCACHE
  environment variable to override this. Also see the
  :vlopt:`--output-split` option and :ref: `Profiling ccache efficiency`

* To reduce the compile time of classes that use a Verilated module (e.g. a
  top CPP file) you may wish to add a
  :option:`/*verilator&32;no_inline_module*/` metacomment to your top level
  module. This will decrease the amount of code in the model's Verilated
  class, improving compile times of any instantiating top level C++ code,
  at a relatively small cost of execution performance.

* Use :ref:`hierarchical verilation`.


Why do so many files need to recompile when I add a signal?
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

Adding a new signal requires the symbol table to be recompiled.  Verilator
uses one large symbol table, as that results in 2-3 less assembly
instructions for each signal access.  This makes the execution time 10-15%
faster, but can result in more compilations when something changes.


How do I access Verilog functions/tasks in C?
"""""""""""""""""""""""""""""""""""""""""""""

Use the SystemVerilog Direct Programming Interface.  You write a Verilog
function or task with input/outputs that match what you want to call in
with C.  Then mark that function as a DPI export function.  See the DPI
chapter in the IEEE Standard.


How do I access C++ functions/tasks in Verilog?
"""""""""""""""""""""""""""""""""""""""""""""""

Use the SystemVerilog Direct Programming Interface.  You write a Verilog
function or task with input/outputs that match what you want to call in
with C.  Then mark that function as a DPI import function.  See the DPI
chapter in the IEEE Standard.


How do I access signals in C?
"""""""""""""""""""""""""""""

The best thing to do is to make a SystemVerilog "export DPI" task or
function that accesses that signal, as described in the DPI chapter in the
manual and DPI tutorials on the web.  This will allow Verilator to better
optimize the model and should be portable across simulators.

If you really want raw access to the signals, declare the signals you will
be accessing with a :option:`/*verilator&32;public*/` metacomment before
the closing semicolon.  Then scope into the C++ class to read the value of
the signal, as you would any other member variable.

Signals are the smallest of 8-bit unsigned chars (equivalent to uint8_t),
16-bit unsigned shorts (uint16_t), 32-bit unsigned longs (uint32_t), or
64-bit unsigned long longs (uint64_t) that fits the width of the signal.
Generally, you can use just uint32_t's for 1 to 32 bits, or uint64_t for
1 to 64 bits, and the compiler will properly up-convert smaller entities.
Note even signed ports are declared as unsigned; you must sign extend
yourself to the appropriate signal width.

Signals wider than 64 bits are stored as an array of 32-bit uint32_t's.
Thus to read bits 31:0, access signal[0], and for bits 63:32, access
signal[1].  Unused bits (for example bit numbers 65-96 of a 65-bit vector)
will always be zero.  If you change the value you must make sure to pack
zeros in the unused bits or core-dumps may result, because Verilator strips
array bound checks where it believes them to be unnecessary to improve
performance.

In the SYSTEMC example above, if you had in our.v:

 .. code-block:: sv

      input clk /*verilator public*/;
      // Note the placement of the semicolon above

From the sc_main.cpp file, you'd then:

 .. code-block:: C++

      #include "Vour.h"
      #include "Vour_our.h"
      cout << "clock is " << top->our->clk << endl;


In this example, clk is a bool you can read or set as any other variable.
The value of normal signals may be set, though clocks shouldn't be changed
by your code or you'll get strange results.


Should a module be in Verilog or SystemC?
"""""""""""""""""""""""""""""""""""""""""

Sometimes there is a block that only interconnects instances, and have a
choice as to if you write it in Verilog or SystemC.  Everything else being
equal, best performance is when Verilator sees all of the design.  So, look
at the hierarchy of your design, labeling instances as to if they are
SystemC or Verilog.  Then:

* A module with only SystemC instances below must be SystemC.

* A module with a mix of Verilog and SystemC instances below must be
  SystemC. (As Verilator cannot connect to lower-level SystemC instances.)

* A module with only Verilog instances below can be either, but for best
  performance should be Verilog.  (The exception is if you have a design
  that is instantiated many times; in this case Verilating one of the lower
  modules and instantiating that Verilated instances multiple times into a
  SystemC module *may* be faster.)
