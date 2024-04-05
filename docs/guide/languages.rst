.. Copyright 2003-2024 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

***************
Input Languages
***************

This section describes the languages Verilator takes as input.  See also
:ref:`Configuration Files`.


Language Standard Support
=========================

Verilog 2001 (IEEE 1364-2001) Support
-------------------------------------

Verilator supports most Verilog 2001 language features.  This includes
signed numbers, "always @\*", generate statements, multidimensional arrays,
localparam, and C-style declarations inside port lists.


Verilog 2005 (IEEE 1364-2005) Support
-------------------------------------

Verilator supports most Verilog 2005 language features.  This includes the
\`begin_keywords and \`end_keywords compiler directives, $clog2, and the
uwire keyword.


SystemVerilog 2005 (IEEE 1800-2005) Support
-------------------------------------------

Verilator supports ==? and !=? operators, ++ and -- in some contexts,
$bits, $countbits, $countones, $error, $fatal, $info, $isunknown, $onehot,
$onehot0, $unit, $warning, always_comb, always_ff, always_latch, bit, byte,
chandle, const, do-while, enum, export, final, import, int, interface,
logic, longint, modport, package, program, shortint, struct, time, typedef,
union, var, void, priority case/if, and unique case/if.

It also supports .name and .\* interconnection.

Verilator partially supports concurrent assert and cover statements; see
the enclosed coverage tests for the allowed syntax.

Verilator has limited support for class and related object-oriented
constructs.


SystemVerilog 2012 (IEEE 1800-2012) Support
-------------------------------------------

Verilator implements a full SystemVerilog-compliant preprocessor, including
function call-like preprocessor defines, default define arguments,
\`__FILE__, \`__LINE__ and \`undefineall.


SystemVerilog 2017 (IEEE 1800-2017) Support
-------------------------------------------

Verilator supports the 2017 "for" loop constructs and several cleanups IEEE
made in 1800-2017.


SystemVerilog 2023 (IEEE 1800-2023) Support
-------------------------------------------

Verilator supports some of the 2023 improvements, including triple-quoted
string blocks that may include newlines and single quotes.

Verilator implements a full IEEE 1800-2023 compliant preprocessor,
including triple-quoted strings, and \`ifdef expressions.


Verilog AMS Support
-------------------

Verilator implements a very small subset of Verilog AMS (Verilog Analog and
Mixed-Signal Extensions) with the subset corresponding to those VMS
keywords with near-equivalents in Verilog IEEE 1364 or SystemVerilog
IEEE 1800.

AMS parsing is enabled with :vlopt:`--language VAMS <--language>` or
:vlopt:`--language 1800+VAMS <--language>`.

Verilator implements ceil, exp, floor, ln, log, pow, sqrt, string, and
wreal.


Synthesis Directive Assertion Support
-------------------------------------

With the :vlopt:`--assert` option, Verilator reads any

:code:`//synopsys full_case` or :code:`//synopsys parallel_case`
directives.  The same applies to any :code:`//ambit synthesis`,
:code:`//cadence` or :code:`//pragma` directives of the same form.

When these synthesis directives are discovered, Verilator will either
formally prove the directive to be true, or, failing that, will insert the
appropriate code to detect failing cases at simulation runtime and print an
"Assertion failed" error message.

Verilator likewise also asserts any "unique" or "priority" SystemVerilog
keywords on case statements, as well as "unique" on if statements.  However,
"priority if" is currently ignored.


Time
====

With :vlopt:`--timing`, all timing controls are supported:

* delay statements,
* event control statements not only at the top of a process,
* intra-assignment timing controls,
* net delays,
* :code:`wait` statements,

as well as all flavors of :code:`fork`.

Compiling a Verilated design that uses these features requires a
compiler with C++20 coroutine support, e.g. Clang 5, GCC 10, or newer.

:code:`#0` delays cause Verilator to issue the :option:`ZERODLY` warning, as
they work differently than described in the LRM. They do not schedule process
resumption in the Inactive region, though the process will get resumed in the
same time slot.

Rising/falling/turn-off delays are currently unsupported and cause the
:option:`RISEFALLDLY` warning.

Minimum/typical/maximum delays are currently unsupported. The typical delay is
always the one chosen. Such expressions cause the :option:`MINTYPMAX` warning.

Another consequence of using :vlopt:`--timing` is that the :vlopt:`--main`
option generates a main file with a proper timing eval loop, eliminating the
need for writing any driving C++ code. You can simply compile the
simulation (perhaps using :vlopt:`--build`) and run it.

With :vlopt:`--no-timing`, all timing controls cause the :option:`NOTIMING`
error, except:

* delay statements - they are ignored (as they are in synthesis), though they
  do issue a :option:`STMTDLY` warning,
* intra-assignment timing controls - they are ignored, though they do issue an
  :option:`ASSIGNDLY` warning,
* net delays - they are ignored,
* event controls at the top of the procedure,

Forks cause this error as well, except:

* forks with no statements,
* :code:`fork..join` or :code:`fork..join_any` with one statement,
* forks with :vlopt:`--bbox-unsup`.

If neither :vlopt:`--timing` nor :vlopt:`--no-timing` is specified, all
timing controls cause the :option:`NEEDTIMINGOPT` error, except event
controls at the top of the process. Forks cause this error as well, except:

* forks with no statements,
* :code:`fork..join` or :code:`fork..join_any` with one statement,
* forks with :vlopt:`--bbox-unsup`.

Timing controls and forks can also be ignored in specific files or parts of
files. The :option:`/*verilator&32;timing_off*/` and
:option:`/*verilator&32;timing_off*/` metacomments will make Verilator ignore
the encompassed timing controls and forks, regardless of the chosen
:vlopt:`--timing` or :vlopt:`--no-timing` option. This can also be achieved
using the :option:`timing_off` and :option:`timing_off` options in Verilator
configuration files.


.. _Language Limitations:

Language Limitations
====================

This section describes the language limitations of Verilator. Many of these
restrictions are by intent.

Synthesis Subset
----------------

Verilator supports the Synthesis subset with other verification constructs
being added over time. Verilator also simulates events as Synopsys's Design
Compiler would, namely given a block of the form:

.. code-block:: sv

        always @(x) y = x & z;

This will recompute y when there is a potential for change in x or a change
in z; that is when the flops computing x or z evaluate (which is what
Design Compiler will synthesize.)  A compliant simulator will only
calculate y if x changes.  We recommend using always_comb to make the code
run the same everywhere.  Also avoid putting $displays in combo blocks, as
they may print multiple times when not desired, even on compliant
simulators as event ordering is not specified.


Signal Naming
-------------

To avoid conflicts with C symbol naming, any character in a signal name
that is not alphanumeric nor a single underscore will be replaced by __0hh
where hh is the hex code of the character. To avoid conflicts with
Verilator's internal symbols, any double underscore is replaced with
___05F (5F is the hex code of an underscore.)


Bind
----

Verilator only supports bind to a target module name, not to an
instance path.


Class
-----

Verilator class support is limited but in active development.  Verilator
supports members, methods, class extend, and class parameters.


Dotted cross-hierarchy references
---------------------------------

Verilator supports dotted references to variables, functions, and tasks in
different modules. The portion before the dot must have a constant value;
for example a[2].b is acceptable, while a[x].b is generally not.

References into generated and arrayed instances use the instance names
specified in the Verilog standard; arrayed instances are named
``{instanceName}[{instanceNumber}]`` in Verilog, which becomes
``{instanceName}__BRA__{instanceNumber}__KET__`` inside the generated C++
code.


Latches
-------

Verilator is optimized for edge-sensitive (flop-based) designs.  It will
attempt to do the correct thing for latches, but most performance
optimizations will be disabled around the latch.


Structures and Unions
---------------------

All structures and unions are scheduled together, which means that
generating one member of a structure from blocking, and another from
non-blocking assignments is unsupported.


.. _Unknown States:

Unknown States
--------------

Verilator is mostly a two-state simulator, not a four-state simulator.
However, it has two features that uncover most initialization bugs
(including many that a four-state simulator will miss.)

Identity comparisons (=== or !==) are converted to standard ==/!= when
neither side is a constant.  This may make the expression yield a different
result than a four-state simulator.  An === comparison to X will
always be false, so that Verilog code which checks for uninitialized logic
will not fire.

Assigning X to a variable will assign a constant value as determined by the
:vlopt:`--x-assign` option.  This allows runtime randomization; thus, if
the value is used, the random value should cause downstream errors.
Integers also get randomized, even though the Verilog 2001 specification
says they initialize to zero.  However, randomization happens at
initialization time; hence, during a single simulation run, the same
constant (but random) value will be used every time the assignment is
executed.

All variables, depending on :vlopt:`--x-initial` setting, are typically
randomly initialized using a function.  You can determine that reset is
working correctly by running several random simulation runs.  On the first
run, have the function initialize variables to zero.  On the second, have
it initialize variables to one.  On the third and following runs, have it
initialize them randomly.  If the results match, reset works.  (Note that
this is what the hardware will do.)  In practice, setting all variables to
one at startup finds the most problems (since control signals are typically
active-high).

:vlopt:`--x-assign` applies to variables explicitly initialized or assigned
an X. Uninitialized clocks are initialized to zero, while all other state
holding variables are initialized to a random value.  Event-driven
simulators will generally trigger an edge on a transition from X to 1
(posedge) or X to 0 (negedge). However, by default, since clocks are
initialized to zero, Verilator will not trigger an initial negedge. Some
code (particularly for reset) may rely on X->0 triggering an edge. The
:vlopt:`--x-initial-edge` option enables this behavior. Comparing runs with
and without this option will find such problems.


Tri/Inout
---------

Verilator converts some simple tristate structures into two state.  Pullup,
pulldown, bufif0, bufif1, notif0, notif1, pmos, nmos, tri0 and tri1 are
also supported.  Simple comparisons with :code:`=== 1'bz` are also
supported.

An assignment of the form:

.. code-block:: sv

        inout driver;
        wire driver = (enable) ? output_value : 1'bz;

Will be converted to:

.. code-block:: sv

        input driver;       // Value being driven in from "external" drivers
        output driver__en;  // True if driven from this module
        output driver__out; // Value being driven from this module

External logic will be needed to combine these signals with any external
drivers.

Tristate drivers are not supported inside functions and tasks; an inout
there will be considered a two-state variable that is read and written
instead of a four-state variable.


Gate Primitives
---------------

The 2-state gate primitives (and, buf, nand, nor, not, or, xnor, xor) are
directly converted to behavioral equivalents.  The 3-state and MOS gate
primitives are not supported.  Tables are not supported.


Specify blocks
--------------

All specify blocks and timing checks are ignored. All min:typ:max delays
use the typical value.


Array Initialization
--------------------

When initializing a large array, you need to use non-delayed assignments.
Verilator will tell you when this needs to be fixed; see the BLKLOOPINIT
error for more information.


Array Out of Bounds
-------------------

Writing a memory element outside the bounds specified for the array may
cause a different memory element inside the array to be written instead.
For power-of-2 sized arrays, Verilator will give a width warning and the
address.  For non-power-of-2-sizes arrays, index 0 will be written.

Reading a memory element outside the bounds specified for the array will
give a width warning and wrap around the power-of-2 size.  For
non-power-of-2 sizes, it will return an unspecified constant of the
appropriate width.


Assertions
----------

Verilator is beginning to add support for assertions.  Verilator currently
only converts assertions to simple :code:`if (...) error` statements, and
coverage statements to increment the line counters described in the
coverage section.

Verilator does not support SEREs yet.  All assertion and coverage
statements must be simple expressions that complete in one cycle.


Encrypted Verilog
-----------------

Open-source simulators like Verilator cannot use encrypted RTL
(i.e. IEEE P1735).  Talk to your IP vendor about delivering IP blocks via
Verilator's :vlopt:`--protect-lib` feature.


Language Keyword Limitations
============================

This section describes specific limitations for each language keyword.

.. Hack to get long definition list:
.. |cmdslong1| replace:: \`__FILE__, \`__LINE__, \`begin_keywords,
   \`begin_keywords, \`begin_keywords, \`begin_keywords, \`begin_keywords,
   \`define, \`else, \`elsif, \`end_keywords, \`endif, \`error, \`ifdef,
   \`ifndef, \`include, \`line, \`systemc_ctor, \`systemc_dtor,
   \`systemc_header, \`systemc_imp_header, \`systemc_implementation,
   \`systemc_interface, \`undef, \`verilog

|cmdslong1|
  Fully supported.


.. Hack to get long definition list:

.. |cmdslong2| replace:: always, always_comb, always_ff, always_latch, and,
   assign, begin, buf, byte, case, casex, casez, default, defparam,
   do-while, else, end, endcase, endfunction, endgenerate, endmodule,
   endspecify, endtask, final, for, function, generate, genvar, if,
   initial, inout, input, int, integer, localparam, logic, longint,
   macromodule, module, nand, negedge, nor, not, or, output, parameter,
   posedge, reg, scalared, shortint, signed, supply0, supply1, task, time,
   tri, typedef, var, vectored, while, wire, xnor, xor

|cmdslong2|
  Generally supported.

++, -- operators
  Increment/decrement can only be used as standalone statements or in
  certain limited cases.

'{} operator
  Assignment patterns with an order based, default, constant integer (array)
  or member identifier (struct/union) keys are supported.  Data type keys
  and keys computed from a constant expression are not supported.

\`uselib
  Uselib, a vendor-specific library specification method, is ignored along
  with anything following it until the end of that line.

cast operator
  Casting is supported only between simple scalar types, signed and
  unsigned, not arrays nor structs.

chandle
  Treated as a "longint"; does not yet warn about operations specified as
  illegal on chandles.

checker
  Treated as a "module"; does not yet warn about many constructs illegal
  inside a checker.

disable
  Disable statements may be used only if the block being disabled is a
  block the disable statement itself is inside.  This was commonly used to
  provide loop break and continue functionality before SystemVerilog added
  the break and continue keywords.

force, release
  Verilator supports the procedural `force` (and corresponding `release`)
  statement. However, the behavior of the `force` statement does not
  entirely comply with IEEE 1800. According to the standard, when a
  procedural statement of the form `force a = b;` is executed, the
  simulation should behave as if, from that point forwards, a continuous
  assignment `assign a = b;` has been added to override the drivers of `a`.
  More specifically: the value of `a` should be updated whenever the value
  of `b` changes, until a `release a;` statement is executed.  Verilator
  instead evaluates the current value of `b` when the `force` statement is
  executed, and forces `a` to that value, without updating it until a new
  `force` or `release` statement is encountered that applies to `a`. This
  non-standard behavior is nevertheless consistent with some other
  simulators.

inside
  Inside expressions may not include unpacked array traversal or $ as an
  upper bound.  Case inside and case matches are also unsupported.

interface
  Interfaces and modports, including generated data types are
  supported.  Generate blocks around modports are not supported, nor are
  virtual interfaces nor unnamed interfaces.

shortreal
  Short floating point (shortreal) numbers are converted to real. Most
  other simulators either do not support float, or convert likewise.

specify specparam
  All specify blocks and timing checks are ignored.

uwire
  Verilator does not perform warning checking on uwires; it treats the
  uwire keyword as if it were the normal wire keyword.

$bits, $countbits, $countones, $finish, $isunknown, $onehot, $onehot0, $signed, $stime, $stop, $time, $unsigned,
  Generally supported.

$dump/$dumpports and related
  $dumpfile or $dumpports will create a VCD or FST file (based on
  the :vlopt:`--trace` option given when the model was Verilated). This
  will take effect starting at the next eval() call.  If you have multiple
  Verilated designs under the same C model, this will dump signals
  only from the design containing the $dumpvars.

  $dumpvars and $dumpports module identifier is ignored; the traced
  instances will always start at the top of the design. The levels argument
  is also ignored; use tracing_on/tracing_off pragmas instead.

  $dumpportson/$dumpportsoff/$dumpportsall/$dumpportslimit filename
  argument is ignored; only a single trace file may be active at once.

  $dumpall/$dumpportsall, $dumpon/$dumpportson, $dumpoff/$dumpportsoff, and
  $dumplimit/$dumpportlimit are currently ignored.

$error, $fatal, $info, $warning.
  Generally supported.

$exit, $finish, $stop
  The rarely used optional parameter to $finish and $stop is ignored; $exit
  is aliased to $finish.

$fopen, $fclose, $fdisplay, $ferror, $feof, $fflush, $fgetc, $fgets, $fscanf, $fwrite, $fscanf, $sscanf
  Generally supported.

$fullskew, $hold, $nochange, $period, $recovery, $recrem, $removal, $setup, $setuphold, $skew, $timeskew, $width
  All specify blocks and timing checks are ignored.

$random, $urandom, $urandom_range
  Use :vlopt:`+verilator+seed+\<value\>` runtime option to set the seed if
  there is no $random nor $urandom optional argument to set the seed.
  There is one random seed per C thread, not per module for $random, nor
  per object for random stability of $urandom/$urandom_range.

$readmemb, $readmemh
  Read memory commands are supported.  Verilator and the Verilog
  specification do not include support for readmem to multi-dimensional
  arrays.

$test$plusargs, $value$plusargs
  Supported, but the instantiating C++/SystemC wrapper must call

  .. code-block:: C++

        {VerilatedContext*} ->commandArgs(argc, argv);

  to register the command line before calling $test$plusargs or
  $value$plusargs.
