.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _Connecting:

******************************
Connecting to Verilated Models
******************************

Structure of the Verilated Model
================================

Verilator outputs a :file:`{prefix}.h` header file which defines a class
named :code:`{prefix}` which represents the generated model the user is
supposed to instantiate.  This model class defines the interface of the
Verilated model.

Verilator will additionally create a :file:`{prefix}.cpp` file, together
with additional .h and .cpp files for internals.  See the :file:`examples`
directory in the kit for examples.  See :ref:`Files Read/Written` for
information on all the files Verilator might output.

The output of Verilator will contain a :file:`{prefix}.mk` file that may be
used with Make to build a :file:`{prefix}__ALL.a` library with all required
objects in it.

The generated model class file manages all internal state required by the
model, and exposes the following interface that allows interaction with the
model:

* Top level IO ports are exposed as references to the appropriate internal
  equivalents.

* Public top level module instances are exposed as pointers to allow access
  to :code:`/* verilator public */` items.

* The root of the design hierarchy (as in SystemVerilog :code:`$root`) is
  exposed via the :code:`rootp` member pointer to allow access to model
  internals, including :code:`/* verilator public_flat */` items.


.. _Porting from pre 4.210:

Model interface changes in version 4.210
------------------------------------------

Starting from version 4.210, the model class is an interface object.

Up until Verilator version 4.204 inclusive, the generated model class was
also the instance of the top level instance in the design hierarchy (what
you would refer to with :code:`$root` in SystemVerilog).  This meant that
all internal variables that were implemented by Verilator in the root scope
were accessible as members of the model class itself.  Note there were often
many such variable due to module inlining, including :code:`/* verilator
public_flat */` items.

This means that user code that accesses internal signals in the model
(likely including :code:`/* verilator public_flat */` signals, as they are
often inlined into the root scope) will need to be updated as follows:

* No change required for accessing top level IO signals. These are directly
  accessible in the model class via references.

* No change required for accessing :code:`/* verilator public */` items.
  These are directly accessible via sub-module pointers in the model class.

* Accessing any other internal members, including
  :code:`/* verilator public_flat */` items requires the following changes:

  * Additionally include :file:`{prefix}___024root.h`. This header defines
    type of the :code:`rootp` pointer within the model class. Note the
    :code:`__024` substring is the Verilator escape sequence for the
    :code:`$` character, i.e.: :code:`rootp` points to the Verilated
    SystemVerilog :code:`$root` scope.

  * Replace :code:`modelp->internal->member->lookup` references with
    :code:`modelp->rootp->internal->member->lookup` references, which
    contain one additional indirection via the :code:`rootp` pointer.


.. _Connecting to C++:

Connecting to C++
=================

In C++ output mode (:vlopt:`--cc`), the Verilator generated model class is a
simple C++ class.  The user must write a C++ wrapper and main loop for the
simulation, which instantiates the model class, and link with the Verilated
model.

Refer to ``examples/make_tracing_c`` in the distribution for a detailed
commented example.

Top level IO signals are read and written as members of the model.  You
call the model's :code:`eval()` method to evaluate the model.  When the
simulation is complete call the model's :code:`final()` method to execute
any SystemVerilog final blocks, and complete any assertions. See
:ref:`Evaluation Loop`.



Connecting to SystemC
=====================

In SystemC output mode (:vlopt:`--sc`), the Verilator generated model class
is a SystemC SC_MODULE.  This module will attach directly into a SystemC
netlist as an instantiation.

The SC_MODULE gets the same pinout as the Verilog module, with the
following type conversions: Pins of a single bit become bool.  Pins 2-32
bits wide become uint32_t's.  Pins 33-64 bits wide become sc_bv's or
uint64_t's depending on the :vlopt:`--no-pins64` option.  Wider pins
become sc_bv's.  (Uints simulate the fastest so are used where possible.)

Model internals, including lower level sub-modules are not pure SystemC
code.  This is a feature, as using the SystemC pin interconnect scheme
everywhere would reduce performance by an order of magnitude.


Direct Programming Interface (DPI)
==================================

Verilator supports SystemVerilog Direct Programming Interface import and
export statements.  Only the SystemVerilog form ("DPI-C") is supported, not
the original Synopsys-only DPI.

DPI Example
-----------

In the SYSTEMC example above, if you wanted to import C++ functions into
Verilog, put in our.v:

.. code-block::

    import "DPI-C" function int add (input int a, input int b);

    initial begin
       $display("%x + %x = %x", 1, 2, add(1,2));
    endtask

Then after Verilating, Verilator will create a file Vour__Dpi.h with the
prototype to call this function:

.. code-block:: C++

     extern int add(int a, int b);

From the sc_main.cpp file (or another .cpp file passed to the Verilator
command line, or the link), you'd then:

.. code-block:: C++

     #include "svdpi.h"
     #include "Vour__Dpi.h"
     int add(int a, int b) { return a+b; }


DPI System Task/Functions
-------------------------

Verilator extends the DPI format to allow using the same scheme to
efficiently add system functions.  Use a dollar-sign prefixed system
function name for the import, but note it must be escaped.

.. code-block:: sv

    export "DPI-C" function integer \$myRand;

    initial $display("myRand=%d", $myRand());

Going the other direction, you can export Verilog tasks so they can be
called from C++:

.. code-block:: sv

    export "DPI-C" task publicSetBool;

    task publicSetBool;
       input bit in_bool;
       var_bool = in_bool;
    endtask

Then after Verilating, Verilator will create a file Vour__Dpi.h with the
prototype to call this function:

.. code-block:: C++

     extern void publicSetBool(svBit in_bool);

From the sc_main.cpp file, you'd then:

.. code-block:: C++

     #include "Vour__Dpi.h"
     publicSetBool(value);

Or, alternatively, call the function under the design class.  This isn't
DPI compatible but is easier to read and better supports multiple designs.

.. code-block:: C++

     #include "Vour__Dpi.h"
     Vour::publicSetBool(value);
     // or top->publicSetBool(value);

Note that if the DPI task or function accesses any register or net within
the RTL, it will require a scope to be set. This can be done using the
standard functions within svdpi.h, after the module is instantiated, but
before the task(s) and/or function(s) are called.

For example, if the top level module is instantiated with the name "dut"
and the name references within tasks are all hierarchical (dotted) names
with respect to that top level module, then the scope could be set with

.. code-block:: C++

     #include "svdpi.h"
     ...
     const svScope scope = svGetScopeFromName("TOP.dut");
     assert(scope);  // Check for nullptr if scope not found
     svSetScope(scope);

(Remember that Verilator adds a "TOP" to the top of the module hierarchy.)

Scope can also be set from within a DPI imported C function that has been
called from Verilog by querying the scope of that function. See the
sections on DPI Context Functions and DPI Header Isolation below and the
comments within the svdpi.h header for more information.


DPI Imports that access signals
-------------------------------

If a DPI import accesses a signal through the VPI Verilator will not be
able to know what variables are accessed and may schedule the code
inappropriately.  Ideally pass the values as inputs/outputs so the VPI is
not required.  Alternatively a workaround is to use a non-inlined task as a
wrapper:

.. code-block::

     logic din;

     // This DPI function will read "din"
     import "DPI-C" context function void dpi_that_accesses_din();

     always @(...)
        dpi_din_args(din);

     task dpi_din_args(input din);
        /* verilator no_inline_task */
        dpi_that_accesses_din();
     endtask


DPI Display Functions
---------------------

Verilator allows writing $display like functions using this syntax:

.. code-block::

    import "DPI-C" function void
          \$my_display(input string formatted /*verilator sformat*/ );

The :option:`/*verilator&32;sformat*/` metacomment indicates that this
function accepts a $display like format specifier followed by any number of
arguments to satisfy the format.


DPI Context Functions
---------------------

Verilator supports IEEE DPI Context Functions.  Context imports pass the
simulator context, including calling scope name, and filename and line
number to the C code.  For example, in Verilog:

.. code-block::

    import "DPI-C" context function int dpic_line();
    initial $display("This is line %d, again, line %d\n", `line, dpic_line());

This will call C++ code which may then use the svGet\* functions to read
information, in this case the line number of the Verilog statement that
invoked the dpic_line function:

.. code-block:: C++

    int dpic_line() {
        // Get a scope:  svScope scope = svGetScope();

        const char* scopenamep = svGetNameFromScope(scope);
        assert(scopenamep);

        const char* filenamep = "";
        int lineno = 0;
        if (svGetCallerInfo(&filenamep, &lineno)) {
            printf("dpic_line called from scope %s on line %d\n",
               scopenamep, lineno);
            return lineno;
        } else {
            return 0;
        }
    }

See the IEEE Standard for more information.


DPI Header Isolation
--------------------

Verilator places the IEEE standard header files such as svdpi.h into a
separate include directory, vltstd (VeriLaTor STandarD).  When compiling
most applications $VERILATOR_ROOT/include/vltstd would be in the include
path along with the normal $VERILATOR_ROOT/include.  However, when
compiling Verilated models into other simulators which have their own
svdpi.h and similar standard files with different contents, the vltstd
directory should not be included to prevent picking up incompatible
definitions.


Public Functions
----------------

Instead of DPI exporting, there's also Verilator public functions, which
are slightly faster, but less compatible.


Verification Procedural Interface (VPI)
=======================================

Verilator supports a limited subset of the VPI.  This subset allows
inspection, examination, value change callbacks, and depositing of values
to public signals only.

VPI is enabled with the Verilator :vlopt:`--vpi` option.

To access signals via the VPI, Verilator must be told exactly which signals
are to be accessed.  This is done using the Verilator public pragmas
documented below.

Verilator has an important difference from an event based simulator; signal
values that are changed by the VPI will not immediately propagate their
values, instead the top level header file's :code:`eval()` method must be
called.  Normally this would be part of the normal evaluation (i.e. the
next clock edge), not as part of the value change.  This makes the
performance of VPI routines extremely fast compared to event based
simulators, but can confuse some test-benches that expect immediate
propagation.

Note the VPI by its specified implementation will always be much slower
than accessing the Verilator values by direct reference
(structure->module->signame), as the VPI accessors perform lookup in
functions at simulation runtime requiring at best hundreds of instructions,
while the direct references are evaluated by the compiler and result in
only a couple of instructions.

For signal callbacks to work the main loop of the program must call
:code:`VerilatedVpi::callValueCbs()`.


.. _VPI Example:

VPI Example
-----------

In the below example, we have readme marked read-only, and writeme which if
written from outside the model will have the same semantics as if it
changed on the specified clock edge.

.. code-block:: bash

     cat >our.v <<'EOF'
       module our (input clk);
          reg readme   /*verilator public_flat_rd*/;
          reg writeme  /*verilator public_flat_rw @(posedge clk) */;
          initial $finish;
       endmodule
     EOF

There are many online tutorials and books on the VPI, but an example that
accesses the above signal "readme" would be:

.. code-block:: bash

     cat >sim_main.cpp <<'EOF'
       #include "Vour.h"
       #include "verilated.h"
       #include "verilated_vpi.h"  // Required to get definitions

       uint64_t main_time = 0;   // See comments in first example
       double sc_time_stamp() { return main_time; }

       void read_and_check() {
           vpiHandle vh1 = vpi_handle_by_name((PLI_BYTE8*)"TOP.our.readme", NULL);
           if (!vh1) vl_fatal(__FILE__, __LINE__, "sim_main", "No handle found");
           const char* name = vpi_get_str(vpiName, vh1);
           printf("Module name: %s\n", name);  // Prints "readme"

           s_vpi_value v;
           v.format = vpiIntVal;
           vpi_get_value(vh1, &v);
           printf("Value of v: %d\n", v.value.integer);  // Prints "readme"
       }

       int main(int argc, char** argv, char** env) {
           Verilated::commandArgs(argc, argv);
           const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
           const std::unique_ptr<Vour> top{new Vour{contextp.get()}};

           contextp->internalsDump();  // See scopes to help debug
           while (!contextp->gotFinish()) {
               top->eval();
               VerilatedVpi::callValueCbs();  // For signal callbacks
               read_and_check();
           }
           return 0;
       }
     EOF


.. _Evaluation Loop:

Wrappers and Model Evaluation Loop
==================================

When using SystemC, evaluation of the Verilated model is managed by the
SystemC kernel, and for the most part can be ignored.  When using C++, the
user must call :code:`eval()`, or :code:`eval_step()` and
:code:`eval_end_step()`.

1. When there is a single design instantiated at the C++ level that needs
to evaluate within a given context, call :code:`designp->eval()`.

2. When there are multiple designs instantiated at the C++ level that need
to evaluate within a context, call :code:`first_designp->eval_step()` then
:code:`->eval_step()` on all other designs.  Then call
:code:`->eval_end_step()` on the first design then all other designs.  If
there is only a single design, you would call :code:`eval_step()` then
:code:`eval_end_step()`; in fact :code:`eval()` described above is just a
wrapper which calls these two functions.

When :code:`eval()` (or :code:`eval_step()`) is called Verilator looks for
changes in clock signals and evaluates related sequential always blocks,
such as computing always_ff @ (posedge...) outputs.  Then Verilator
evaluates combinatorial logic.

Note combinatorial logic is not computed before sequential always blocks
are computed (for speed reasons). Therefore it is best to set any non-clock
inputs up with a separate :code:`eval()` call before changing clocks.

Alternatively, if all always_ff statements use only the posedge of clocks,
or all inputs go directly to always_ff statements, as is typical, then you
can change non-clock inputs on the negative edge of the input clock, which
will be faster as there will be fewer :code:`eval()` calls.

For more information on evaluation, see :file:`docs/internals.rst` in the
distribution.


Verilated and VerilatedContext
==============================

Multiple Verilated models may be part of the same simulation context, that
is share a VPI interface, sense of time, and common settings.  This common
simulation context information is stored in a ``VerilatedContext``
structure.  If a ``VerilatedContext`` is not created prior to creating a
model, a default global one is created automatically.

The ``Verilated::`` methods, including the ``Verilated::commandArgs`` call
shown above, call VerilatedContext methods using the default global
VerilatedContext.  (Technically they operate on the last one used by a
given thread.)  If you are using multiple simulation contexts you should
not use the Verilated:: methods, and instead always use VerilatedContext
methods called on the appropriate VerilatedContext object.

For methods available under Verilated and VerilatedContext see
:file:`include/verilated.h` in the distribution.
