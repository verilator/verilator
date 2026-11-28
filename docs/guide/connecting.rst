..
   SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
   SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _connecting:

******************************
Connecting to Verilated Models
******************************

Structure of the Verilated Model
================================

Verilator outputs a :file:`{prefix}.h` header file which defines a class
named ``{prefix}`` which represents the generated model the user is
supposed to instantiate. This model class defines the interface of the
Verilated model.

Verilator will additionally create a :file:`{prefix}.cpp` file, together
with additional .h and .cpp files for internals. See the :file:`examples`
directory in the kit for examples. See :ref:`Files Read/Written` for
information on all the files Verilator might output.

The output of Verilator will contain a :file:`{prefix}.mk` file that may be
used with Make to build a :file:`{prefix}__ALL.a` library with all required
objects in it.

The generated model class file manages all internal state required by the
model, and exposes the following interface that allows interaction with the
model:

- Top level IO ports are exposed as references to the appropriate internal
  equivalents.

- Public top level module instances are exposed as pointers to allow access
  to ``/* verilator public */`` items.

- The root of the design hierarchy (as in SystemVerilog ``$root``) is
  exposed via the ``rootp`` member pointer to allow access to model
  internals, including ``/* verilator public_flat */`` items.


.. _model header include macros:

Model Header Include Macros
---------------------------

Code compiled with the generated :file:`{prefix}.mk`, or with the CMake
``verilate()`` command, gets preprocessor macros that expand to the model
header includes, so user C++ need not hard-code the :vlopt:`--prefix`:

.. code-block:: C++

   #include VM_PREFIX_INCLUDE      // e.g. <Vtop.h>
   #include VM_PREFIX_INCLUDE_DPI  // e.g. <Vtop__Dpi.h>

``VM_PREFIX_INCLUDE_DPI`` is defined only when Verilator generates the
:file:`{prefix}__Dpi.h` header, which is the case for designs with DPI and
also for public-signal access such as :vlopt:`--public-flat-rw`. Using it
otherwise is a compile-time error.

A target built from several models defines each macro once, naming the
first model, as one target has one set of preprocessor definitions. Code
that must reach a second model's header names it directly.


.. _porting from pre 4.210:

Model interface changes in version 4.210
----------------------------------------

Starting from version 4.210, the model class is an interface object.

Up until Verilator version 4.204 inclusive, the generated model class was
also the instance of the top level instance in the design hierarchy (what
you would refer to with ``$root`` in SystemVerilog). This meant that all
internal variables that were implemented by Verilator in the root scope
were accessible as members of the model class itself. Note there were often
many such variable due to module inlining, including ``/* verilator
public_flat */`` items.

This means that user code that accesses internal signals in the model
(likely including ``/* verilator public_flat */`` signals, as they are
often inlined into the root scope) will need to be updated as follows:

- No change required for accessing top level IO signals. These are directly
  accessible in the model class via references.

- No change required for accessing ``/* verilator public */`` items. These
  are directly accessible via sub-module pointers in the model class.

- Accessing any other internal members, including ``/* verilator
  public_flat */`` items requires the following changes:

  - Additionally include :file:`{prefix}___024root.h`. This header defines
    type of the ``rootp`` pointer within the model class. Note the
    ``__024`` substring is the Verilator escape sequence for the ``$``
    character, i.e.: ``rootp`` points to the Verilated SystemVerilog
    ``$root`` scope.

  - Replace ``modelp->internal->member`` references with
    ``modelp->rootp->internal->member`` references, which contain one
    additional indirection via the ``rootp`` pointer.


.. _connecting to c++:

Connecting to C++
=================

In C++ output mode (:vlopt:`--cc`), the Verilator generated model class is
a simple C++ class. The user must write a C++ wrapper and main loop for the
simulation, which instantiates the model class, and link with the Verilated
model.

Refer to ``examples/make_tracing_c`` in the distribution for a detailed
commented example.

Top level IO signals are read and written as members of the model. All
inputs must be sanitized, that is have no bits set above those
corresponding to the width of the Verilog construct;
:vlopt:`--runtime-debug` will assert this is correct.

Call the model's ``eval()`` method to evaluate the model. When the
simulation is complete call the model's ``final()`` method to execute any
SystemVerilog final blocks, and complete any assertions. If using
:vlopt:`--timing`, there are two additional functions for checking if there
are any events pending in the simulation due to delays, and for retrieving
the simulation time of the next delayed event. See :ref:`Evaluation Loop`.


Connecting to SystemC
=====================

In SystemC output mode (:vlopt:`--sc`), the Verilator generated model class
is a SystemC SC_MODULE. This module will attach directly into a SystemC
netlist as an instantiation.

The SC_MODULE gets the same pinout as the Verilog module, with the
following type conversions: Pins of a single bit become bool. Pins 2-32
bits wide become uint32_t's. Pins 33-64 bits wide become sc_bv's or
uint64_t's depending on the :vlopt:`--no-pins64` option. Wider pins become
sc_bv's. (Uints simulate the fastest so are used where possible.)

Model internals, including lower level sub-modules are not pure SystemC
code. This is a feature, as using the SystemC pin interconnect scheme
everywhere would reduce performance by an order of magnitude.


Verilated API
=============

The API to a Verilated model is the C++ headers in the include/ directory
in the distribution. These headers use Doxygen comments, `///` and `//<`,
to indicate and document those functions that are part of the Verilated
public API.

Process-Level Clone APIs
------------------------

Modern operating systems support process-level clone (a.k.a copying,
forking) with system call interfaces in C/C++, e.g., ``fork()`` in Linux.

However, after cloning a parent process, some resources cannot be inherited
in the child process. For example, in POSIX systems, when you fork a
process, the child process inherits all the memory of the parent process.
However, only the thread that called fork is replicated in the child
process. Other threads are not.

Therefore, to support the process-level clone mechanisms, Verilator
supports ``prepareClone()`` and ``atClone()`` APIs to allow the user to
manually re-construct the model in the child process. The two APIs handle
all necessary resources required for releasing and re-initializing before
and after cloning.

The two APIs are supported in the verilated models. Here is an example of
usage with Linux ``fork()`` and ``pthread_atfork`` APIs:

.. code-block:: C++

   // static function pointers to fit pthread_atfork
   static auto prepareClone = [](){ topp->prepareClone(); };
   static auto atClone = [](){ topp->atClone(); };

   // in main function, register the handlers:
   pthread_atfork(prepareClone, atClone, atClone);

For better flexibility, you can also manually call the handlers before and
after ``fork()``.

With the process-level clone APIs, users can create process-level snapshots
for the verilated models. While the Verilator save/restore option provides
persistent and circuit-dependent snapshots, the process-level clone APIs
enable in-memory, circuit-transparent, and highly efficient snapshots.


Direct Programming Interface (DPI)
==================================

Verilator supports SystemVerilog Direct Programming Interface import and
export statements. Only the SystemVerilog form ("DPI-C") is supported, not
the original Synopsys-only DPI.

DPI Example
-----------

In the SYSTEMC example above, if you wanted to import C++ functions into
Verilog, put in our.v:

.. code-block::

   import "DPI-C" function int add (input int a, input int b);

   initial begin
     $display("%x + %x = %x", 1, 2, add(1,2));
   end

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

Rather than hard-coding the prefix, ``#include VM_PREFIX_INCLUDE_DPI`` may
be used instead; see :ref:`Model Header Include Macros`.


DPI Unpacked Structures
-----------------------

Vour__Dpi.h also declares the unpacked structures passed by DPI imports and
exports as C structures, each named as the SystemVerilog typedef declaring
it, without its package or other scope. For example:

.. include:: ../../docs/gen/ex_DPISTRUCT_hdr.rst

To instead use an equivalent declaration from other C code, define
``VL_DPITYPE_{name}_`` before including Vour__Dpi.h, or the model header
Vour.h, which includes Vour__Dpi.h when DPI passes unpacked structures. As
C has no scopes, different structures passed by DPI, even from different
models, need different names.


DPI System Task/Functions
-------------------------

Verilator extends the DPI format to allow using the same scheme to
efficiently add system functions. Use a dollar-sign prefixed system
function name for the import, but note it must be escaped.

.. code-block::

   import "DPI-C" function integer \$myRand;

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

Or, alternatively, call the function under the design class. This isn't DPI
compatible but is easier to read and better supports multiple designs.

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
inappropriately. Ideally pass the values as inputs/outputs so the VPI is
not required. Alternatively a workaround is to use a non-inlined task as a
wrapper:

.. code-block::

   logic din;

   // This DPI function will read "din"
   import "DPI-C" context function void dpi_that_accesses_din();

   always @(...)
     dpi_din_args(din);

   task dpi_din_args(input din);
     // verilator no_inline_task
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

Verilator supports IEEE DPI Context Functions. Context imports pass the
simulator context, including calling scope name, and filename and line
number to the C code. For example, in Verilog:

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
separate include directory, vltstd (VeriLaTor STandarD). When compiling
most applications $VERILATOR_ROOT/include/vltstd would be in the include
path along with the normal $VERILATOR_ROOT/include. However, when compiling
Verilated models into other simulators which have their own svdpi.h and
similar standard files with different contents, the vltstd directory should
not be included to prevent picking up incompatible definitions.


Public Functions
----------------

Instead of DPI exporting, there's also Verilator public functions, which
are slightly faster, but less compatible.


.. _dpi hooks:

DPI Hooks
---------

The :option:`insert_dpihook` control file directive lets C++ code alter the
value of a signal without changing the Verilog source. Verilator inserts a
call to an imported DPI-C function at the signal before optimization, so
the signal stays reachable while the rest of the design is still optimized.

For example, given this design:

.. code-block:: sv

   module top(input clk, input [7:0] d, output [7:0] o);
      sub u_sub(.clk, .d, .o);
   endmodule

   module sub(input clk, input [7:0] d, output [7:0] o);
      logic [7:0] target;
      always_ff @(posedge clk) target <= d;
      assign o = target;
   endmodule

and this control file:

.. code-block::

   `verilator_config
   insert_dpihook -callback "stuck" -var "top.u_sub.target"

Verilator transforms ``sub`` into the equivalent of the following
pseudo-Verilog (simplified, the generated names differ):

.. code-block:: sv

   module sub(input clk, input [7:0] d, output [7:0] o,
              input int __Vdpihook_id[1], input string __Vdpihook_path[1][1],
              input bit __Vdpihook_trigger);
      import "DPI-C" function byte stuck(input int id, input bit trigger,
                                         input logic [7:0] value);
      logic [7:0] target;
      always_ff @(posedge clk) target <= d;

      // Set once, at time zero, when a slot binds "target" of this instance
      bit bound;
      int case_id;
      initial
         for (int i = 0; i < 1; ++i)
            if (__Vdpihook_path[i][0] == "target") begin
               bound = 1;
               case_id = __Vdpihook_id[i];
            end

      wire [7:0] hooked = bound ? stuck(case_id, __Vdpihook_trigger, target) : target;
      assign o = hooked;  // was: assign o = target
   endmodule

``top`` gets the same three ports and passes them on to ``u_sub``; of each
slot's path it passes only the part below ``u_sub``.

Verilator writes the C prototype of the callback into the model's
``__Dpi.h`` header. A callback that forces the signal to zero for case id
1, and otherwise returns the value unchanged, is:

.. code-block:: C++

   #include "Vtop__Dpi.h"

   char stuck(int id, svBit trigger, const svLogicVecVal* value) {
       if (id == 1) return 0;
       return static_cast<char>(value->aval);
   }

The C++ harness binds the hook before the first ``eval()``, and toggles
``__Vdpihook_trigger`` whenever the hooks are to be re-evaluated, here once
per time step:

.. code-block:: C++

   topp->__Vdpihook_path[0][0] = "u_sub";
   topp->__Vdpihook_path[0][1] = "target";
   topp->__Vdpihook_id[0] = 1;
   while (!contextp->gotFinish()) {
       // ... drive clk and d ...
       topp->__Vdpihook_trigger = !topp->__Vdpihook_trigger;
       topp->eval();
       contextp->timeInc(1);
   }

This DPI hook is (re)evaluated whenever one of its input signals changes. A
callback whose result depends on the simulation time, such as a fault that
is only active in a time window, must also be re-evaluated while the signal
does not change; otherwise a window that opens while the signal is stable
would only take effect at the next change of the signal. Therefore every
callback also receives the ``__Vdpihook_trigger`` input, and toggling it
re-evaluates all hooks at the next ``eval()``. The harness thereby decides
the time resolution of such callbacks, for example once per time step as
above, or once per clock cycle.

There are some special cases to consider when using DPI hooks. The callback
function must return a value of the same width as the hooked signal. A
target wider than 64 bits cannot be returned, and instead takes a ``void``
callback and needs a helper signal defined, which is also added as first
argument, e.g. ``output logic [W-1:0] result``. If multiple signals are
hooked to the same callback, the callback must return a value of the same
width as the other hooked signals. Additionally the hooked signals must be
of the same kind, since 4-state vectors, 2-state vectors and integer atoms
such as ``int`` have different C types. If this can not be guaranteed, the
signal must use another callback function. Additionally a signal can only
be hooked once.

The hook carries no information about specific bit positions or bit ranges.
Instead it hands the whole signal to the callback and takes the whole value
back. Which specific bits or bit ranges a fault touches can therefore be
decided in the callback, together with the timing.

The following targets are supported:

- Packed types, including targets wider than 64 bits
- Unpacked aggregates
- Aggregate leaves addressed by path
- Unpacked-array elements
- Signals in generate scopes
- Signals in instances inside generate blocks
- Interface signals

When the configuration is done for Verilator and the hook is inserted the
C++ wrapper must bind the hook. This is done by using the
``__Vdpihook_path[i][j]`` and ``__Vdpihook_id[i]`` ports. The first one
needs to be filled with the path parts ending with the signal for ``[j]``,
and ``[i]`` has one entry per ``insert_dpihook`` directive, so all
configured signals can be faulted at the same time. Each such entry is
referred to as a slot. Additionally each signal path is assigned a case id,
which selects the effect the callback function has on the hooked signal.
Two paths may share an id, in which case the callback treats them alike.
The case id is filled into ``__Vdpihook_id[i]`` and is passed to the
callback function as ``input int id``.

To bind a signal to a slot, the path below the top module must be
specified. This is done by filling the ``__Vdpihook_path[i]`` array with
the path parts, with every instance on the way to the signal being one path
part, and the last part being the signal. For example, ``-var
"top.cpu.regfile.data"`` is bound by filling ``__Vdpihook_path[i]`` with
``"cpu"``, ``"regfile"`` and ``"data"``. When the signal is in the top
module, only the signal name is filled in, e.g. ``-var "top.v"`` with
``"v"`` only. Interface instances, including elements of an interface array
such as ``arr[0]``, also count as instances. This is the same way for
standard signals, but some signals are addressed in a special form:

- A generate block does not take a path part of its own. Its name is
  written in front of the next part, separated by a dot, so an instance
  inside a generate block is the single part ``lane[0].u`` (not ``lane[0]``
  followed by ``u``), a signal declared in one is ``lane[0].q``, and nested
  blocks give ``outer[0].inner[1].q``.
- A signal in form of a struct member is named in the last part together
  with its struct, e.g. ``s.a``.
- A signal in form of an element of an unpacked array is named with its
  declared index, e.g. ``mem[2]``, or ``m[5]`` for an array declared as
  ``m[4:7]``.

The ports must be written before the first ``eval()``, the same ordering
that applies to any other model input. The binding is sampled once, at time
zero, so writing the ports later binds nothing; that mistake is reported
with a runtime warning when the simulation ends.

If a slot in the wrapper to bind a path does not match any existing path,
the slot is reported with a runtime warning.

It is important to note that reads are redirected within the module
declaring the target, for an interface signal in every module accessing it,
and where a read reaches the signal through a cross-module hierarchical
reference. The changing effect propagates outwards through ports and
interface connections.


Verification Procedural Interface (VPI)
=======================================

Verilator supports a limited subset of the VPI. This subset allows
inspection, examination, value change callbacks, and depositing of values
to public signals only.

VPI is enabled with the Verilator :vlopt:`--vpi` option.

To access signals via the VPI, Verilator must be told exactly which signals
are to be accessed. This is done using the Verilator public pragmas
documented below.

Verilator has an important difference from an event based simulator; signal
values that are changed by the VPI will not immediately propagate their
values, instead the top level header file's ``eval()`` method must be
called. Normally this would be part of the normal evaluation (i.e. the next
clock edge), not as part of the value change. This makes the performance of
VPI routines extremely fast compared to event based simulators, but can
confuse some test-benches that expect immediate propagation.

Note the VPI by its specified implementation will always be much slower
than accessing the Verilator values by direct reference
(structure->module->signame), as the VPI accessors perform lookup in
functions at simulation runtime requiring at best hundreds of instructions,
while the direct references are evaluated by the compiler and result in
only a couple of instructions.

For signal callbacks to work the main loop of the program must call
``VerilatedVpi::callValueCbs()``.

Verilator also tracks when the model state has been modified via the VPI
with an ``evalNeeded`` flag. This flag can be checked with
``VerilatedVpi::evalNeeded()`` and it can be cleared with
``VerilatedVpi::clearEvalNeeded()``. Used together it is possible to skip
``eval()`` calls if no model state has been changed since the last
``eval()``.

Any data written via ``vpi_put_value`` with ``vpiInertialDelay`` will be
deferred for later. These delayed values can be flushed to the model with
``VerilatedVpi::doInertialPuts()``.


.. _vpi example:

VPI Example
-----------

In the below example, we have readme marked read-only, and writeme marked
read-write which if written from outside the model will have the same
semantics as if it was a top level input.

.. code-block:: bash

   cat >our.v <<'EOF'
     module our #(
        parameter WIDTH /*verilator public_flat_rd*/ = 32
     ) (input clk);
       reg [WIDTH-1:0] readme   /*verilator public_flat_rd*/;
       reg [WIDTH-1:0] writeme  /*verilator public_flat_rw*/;
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
         const char* type = vpi_get_str(vpiType, vh1);
         const int size = vpi_get(vpiSize, vh1);
         printf("register name: %s, type: %s, size: %d\n", name, type, size);  // Prints "register name: readme, type: vpiReg, size: 32"

         s_vpi_value v;
         v.format = vpiIntVal;
         vpi_get_value(vh1, &v);
         printf("Value of %s: %d\n", name, v.value.integer);  // Prints "Value of readme: 0"
     }

     int main(int argc, char** argv) {
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


.. _evaluation loop:

Wrappers and Model Evaluation Loop
==================================

When using SystemC, evaluation of the Verilated model is managed by the
SystemC kernel, and for the most part can be ignored. When using C++, the
user must call ``eval()``, or ``eval_step()`` and ``eval_end_step()``.

1. When there is a single design instantiated at the C++ level that needs
to evaluate within a given context, call ``designp->eval()``.

2. When there are multiple designs instantiated at the C++ level that need
to evaluate within a context, call ``first_designp->eval_step()`` then
``->eval_step()`` on all other designs. Then call ``->eval_end_step()`` on
the first design then all other designs. If there is only a single design,
you would call ``eval_step()`` then ``eval_end_step()``; in fact ``eval()``
described above is just a wrapper which calls these two functions.

3. If using delays and :vlopt:`--timing`, there are two additional methods
the user should call:

   - ``designp->eventsPending()``, which returns ``true`` if there are any
     delayed events pending,
   - ``designp->nextTimeSlot()``, which returns the simulation time of the
     next delayed event. This method can only be called if
     ``designp->eventsPending()`` returned ``true``.

Call ``eventsPending()`` to check if you should continue with the
simulation, and then ``nextTimeSlot()`` to move simulation time forward.
:vlopt:`--main` can be used with :vlopt:`--timing` to generate a basic
example of a timing-enabled eval loop.

When ``eval()`` (or ``eval_step()``) is called Verilator looks for changes
in clock signals and evaluates related sequential always blocks, such as
computing always_ff @ (posedge...) outputs. With :vlopt:`--timing`, it
resumes any delayed processes awaiting the current simulation time. Then
Verilator evaluates combinational logic.

Note combinatorial logic is not computed before sequential always blocks
are computed (for speed reasons). Therefore it is best to set any non-clock
inputs up with a separate ``eval()`` call before changing clocks.

Alternatively, if all always_ff statements use only the posedge of clocks,
or all inputs go directly to always_ff statements, as is typical, then you
can change non-clock inputs on the negative edge of the input clock, which
will be faster as there will be fewer ``eval()`` calls.

For more information on evaluation, see :file:`docs/internals.rst` in the
distribution.


Verilated and VerilatedContext
==============================

Multiple C++ Verilated models may be part of the same simulation context,
that is share a VPI interface, sense of time, and common settings. This
common simulation context information is stored in a ``VerilatedContext``
structure. If a ``VerilatedContext`` is not created prior to creating a
model, a default global one is created automatically. SystemC requires
using only the single, default VerilatedContext.

The ``Verilated::`` methods, including the ``Verilated::commandArgs`` call
shown above, call VerilatedContext methods using the default global
VerilatedContext. (Technically they operate on the last one used by a given
thread.) If you are using multiple simulation contexts you should not use
the Verilated:: methods, and instead always use VerilatedContext methods
called on the appropriate VerilatedContext object.

For methods available under Verilated and VerilatedContext see
:file:`include/verilated.h` in the distribution.
