.. Copyright 2003-2023 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

*******************
Errors and Warnings
*******************

.. _Disabling Warnings:

Disabling Warnings
==================

Warnings may be disabled in multiple ways:

#. Disable the warning globally by invoking Verilator with the
   :code:`-Wno-{warning-code}` option.

   Global disables should be avoided, as they removes all checking across
   the source files, and prevents other users from compiling the sources
   without knowing the magic set of disables needed to compile those
   sources successfully.

#. Disable the warning in the design source code.  When the warning is
   printed, it will include a warning code.  Surround the offending line
   with a :code:`/*verilator&32;lint_off*/` and
   :code:`/*verilator&32;lint_on*/` metacomment pair:

   .. code-block:: sv

         // verilator lint_off UNSIGNED
         if (`DEF_THAT_IS_EQ_ZERO <= 3) $stop;
         // verilator lint_on UNSIGNED


   A lint_off in the design source code will propagate down to any child
   files (files later included by the file with the lint_off), but will not
   propagate upwards to any parent file (file that included the file with
   the lint_off).

#. Disable the warning using :ref:`Configuration Files` with a
   :option:`lint_off` command.  This is useful when a script suppresses
   warnings, and the Verilog source should not be changed.  This method also
   allows matching on the warning text.

   .. code-block:: sv

         lint_off -rule UNSIGNED -file "*/example.v" -line 1


Error And Warning Format
========================

Warnings and errors printed by Verilator always match this regular
expression:

.. code-block::

         %(Error|Warning)(-[A-Z0-9_]+)?: ((\S+):(\d+):((\d+):)? )?.*


Errors and warnings start with a percent sign (historical heritage from
Digital Equipment Corporation).  Some errors or warnings have a code
attached, with meanings described below.  Some errors also have a filename,
line number, and optional column number (starting at column 1 to match GCC).

Following the error message, Verilator will typically show the user's
source code corresponding to the error, prefixed by the line number and a "
| ".  Following this is typically an arrow and ~ pointing at the error on
the source line directly above.


List Of Warnings
================

.. option:: Internal Error

   This error should never occur first, though it may occur if earlier
   warnings or error messages have corrupted the program.  If there are no
   other warnings or errors, submit a bug report.


.. option:: Unsupported: ....

   This error indicates that the code uses a Verilog language construct
   that is not yet supported in Verilator.  See also :ref:`Language
   Limitations`.


.. option:: ALWCOMBORDER

   .. TODO better example

   Warns that an :code:`always_comb` block has a variable that is set
   after it is used.  This may cause simulation-synthesis mismatches, as
   not all simulators allow this ordering.

   .. code-block:: sv

         always_comb begin
            a = b;
            b = 1;
         end

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: ASCRANGE

   .. TODO better example

   Warns that a packed vector is declared with ascending bit range
   (i.e. [0:7]).  Descending bit range is now the overwhelming standard,
   and ascending ranges are now thus often due to simple oversight
   instead of intent (a notable exception is the OpenPOWER code base).

   It also warns that an instance is declared with ascending range
   (i.e. [0:7] or [7]) and is connected to an N-wide signal.
   The bits will likely be in the reversed order from what people may expect
   (i.e., instance [0] will connect to signal bit [N-1] not bit [0]).

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: ASSIGNDLY

   .. TODO better example

   Warns that the code has an assignment statement with a delayed time in
   front of it, for example:

   .. code-block:: sv

         a <= #100 b;
         assign #100 a = b;

   Ignoring this warning may make Verilator simulations differ from other
   simulators; however, this was a common style at one point, so disabled
   by default as a code-style warning.

   This warning is issued only if Verilator is run with :vlopt:`--no-timing`.


.. option:: ASSIGNIN

   .. TODO better example

   An error that an assignment is being made to an input signal.  This is
   almost certainly a mistake, though technically legal.

   .. code-block:: sv

         input a;
         assign a = 1'b1;

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: BADSTDPRAGMA

   An error that a pragma is badly formed, for pragmas defined by IEEE
   1800-2017.  For example, an empty pragma line, or an incorrectly used
   'pragma protect'.  Third-party pragmas not defined by IEEE 1800-2017 are
   ignored.


.. option:: BLKANDNBLK

   .. TODO better example

   BLKANDNBLK is an error that a variable is driven by a mix of blocking and
   non-blocking assignments.

   This is not illegal in SystemVerilog but a violation of good coding
   practice. Verilator reports this as an error because ignoring this
   warning may make Verilator simulations differ from other simulators.

   It is generally safe to disable this error (with a
   :code:`// verilator lint_off BLKANDNBLK` metacomment or the
   :code:`-Wno-BLKANDNBLK` option) when one of the assignments is inside a
   public task, or when the blocking and non-blocking assignments have
   non-overlapping bits and structure members.

   Generally, this is caused by a register driven by both combo logic and a
   flop:

   .. code-block:: sv

         logic [1:0] foo;
         always @(posedge clk)  foo[0] <= ...
         always_comb foo[1] = ...

   Instead, use a different register for the flop:

   .. code-block:: sv

         logic [1:0] foo;
         always @(posedge clk)  foo_flopped[0] <= ...
         always_comb foo[0] = foo_flopped[0];
         always_comb foo[1] = ...

   Or, this may also avoid the error:

   .. code-block:: sv

         logic [1:0] foo /*verilator split_var*/;


.. option:: BLKLOOPINIT

   .. TODO better example

   This indicates that the initialization of an array needs to use
   non-delayed assignments.  This is done in the interest of speed; if
   delayed assignments were used, the simulator would have to copy large
   arrays every cycle.  (In smaller loops, loop unrolling allows the
   delayed assignment to work, though it's a bit slower than a non-delayed
   assignment.)  Here's an example

   .. code-block:: sv

         always @(posedge clk)
            if (~reset_l)
                for (i=0; i<`ARRAY_SIZE; i++)
                    array[i] = 0;  // Non-delayed for verilator


   This message is only seen on large or complicated loops because
   Verilator generally unrolls small loops.  You may want to try increasing
   :vlopt:`--unroll-count` (and occasionally :vlopt:`--unroll-stmts`), which
   will raise the small loop bar to avoid this error.


.. option:: BLKSEQ

   .. TODO better example

   This indicates that a blocking assignment (=) is used in a sequential
   block.  Generally, non-blocking/delayed assignments (<=) are used in
   sequential blocks, to avoid the possibility of simulator races.  It can
   be reasonable to do this if the generated signal is used ONLY later in
   the same block; however, this style is generally discouraged as it is
   error prone.

   .. code-block:: sv

         always @(posedge clk)  foo = ...;  //<--- Warning

   Disabled by default as this is a code-style warning; it will simulate
   correctly.

   Other tools with similar warnings: Verible's always-ff-non-blocking,
   "Use only non-blocking assignments inside 'always_ff' sequential
   blocks."


.. option:: BSSPACE

   .. TODO better example

   Warns that a backslash is followed by a space then a newline. Likely the
   intent was to have a backslash directly followed by a newline (e.g.,
   when making a "\`define"), and there's accidentally white space at the
   end of the line.  If the space is not accidental, suggest removing the
   backslash in the code, as it serves no function.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: CASEINCOMPLETE

   .. TODO better example

   Warns that inside a case statement, there is a stimulus pattern for
   which no case item is provided.  This is bad style; if a case is
   impossible, it's better to have a :code:`default: $stop;` or just
   :code:`default: ;` so that any design assumption violations will be
   discovered in the simulation.

   Unique case statements that select on an enumerated variable, where all
   of the enumerated values are covered by case items, are considered
   complete even if the case statement does not cover illegal
   non-enumerated values (IEEE 1800-2017 12.5.3).  To check that illegal
   values are not hit, use :vlopt:`--assert`.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: CASEOVERLAP

   .. TODO better example

   Warns that a case statement has case values detected to be overlapping.
   This is bad style, as moving the order of case values will cause
   different behavior.  Generally the values can be respecified not to
   overlap.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: CASEWITHX

   .. TODO better example

   Warns that a case statement contains a constant with an ``x`` .
   Verilator is two-state so interpret such items as always false.  Note that a
   frequent error is to use a ``X`` in a case or casez statement item; often,
   what the user instead intended is to use a casez with ``?`` .

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: CASEX

   .. TODO better example

   Warns that it is better style to use casez, and "?" in place of
   "x"'s.  See
   `http://www.sunburst-design.com/papers/CummingsSNUG1999Boston_FullParallelCase_rev1_1.pdf
   <http://www.sunburst-design.com/papers/CummingsSNUG1999Boston_FullParallelCase_rev1_1.pdf>`_

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: CASTCONST

   .. TODO better example

   Warns that a dynamic cast ($cast) is unnecessary as the $cast will
   always succeed or fail.  If it will always fail, the $cast is useless,
   and if it will always succeed, a static cast may be preferred.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.  On other simulators, not fixing CASTCONST may
   result in decreased performance.


.. option:: CDCRSTLOGIC

   Historical, never issued since version 5.008.

   Warned with a no longer supported clock domain crossing option that
   asynchronous flop reset terms came from other than primary inputs or
   flopped outputs, creating the potential for reset glitches.


.. option:: CLKDATA

   Historical, never issued since version 5.000.

   Warned that clock signal was mixed used with/as a data signal. The
   checking for this warning was enabled only if the user has explicitly
   marked some signal as clocker using the command line option or in-source
   meta comment (see :vlopt:`--clk`).

   The warning could be disabled without affecting the simulation
   result. But it was recommended to check the warning as it may have
   degraded the performance of the Verilated model.


.. option:: CMPCONST

   .. TODO better example

   Warns that the code is comparing a value in a way that will always be
   constant.  For example, :code:`X > 1` will always be true when X is a
   single bit wide.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: COLONPLUS

   Warns that a :code:`:+` is seen. Likely the intent was to use :code:`+:`
   to select a range of bits. If the intent was an explicitly positive
   range, suggest adding a space, e.g., use :code:`: +`.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: COMBDLY

   .. TODO better example

   Warns that there is a delayed assignment inside of a combinatorial
   block.  Using delayed assignments in this way is considered bad form,
   and may lead to the simulator not matching synthesis.  If this message
   is suppressed, Verilator, like synthesis, will convert this to a
   non-delayed assignment, which may result in logic races or other
   nasties.  See
   `http://www.sunburst-design.com/papers/CummingsSNUG2000SJ_NBA_rev1_2.pdf
   <http://www.sunburst-design.com/papers/CummingsSNUG2000SJ_NBA_rev1_2.pdf>`_

   Ignoring this warning may make Verilator simulations differ from other
   simulators.


.. option:: CONSTRAINTIGN

   Warns that Verilator does not support :code:`constraint`,
   :code:`constraint_mode`, or :code:`rand_mode`, and the construct was are
   ignored.

   Ignoring this warning may make Verilator randomize() simulations differ
   from other simulators.


.. option:: CONTASSREG

   .. TODO better example

   An error that a continuous assignment is setting a reg. According to IEEE
   Verilog, but not SystemVerilog, a wire must be used as the target of
   continuous assignments.

   This error is only reported when

   :vlopt:`--language 1364-1995 <--language>`,
   :vlopt:`--language 1364-2001 <--language>`, or
   :vlopt:`--language 1364-2005 <--language>` is used.

   Ignoring this error will only suppress the lint check; it will simulate
   correctly.


.. option:: DECLFILENAME

   .. TODO better example

   Warns that a module or other declaration's name doesn't match the
   filename with the path and extension stripped that it is declared in.  The
   filename a module/interface/program is declared in should match the
   name of the module etc., so that :vlopt:`-y` option directory searching
   will work.  This warning is printed for only the first mismatching
   module in any given file, and :vlopt:`-v` library files are ignored.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.


.. option:: DEFPARAM

   Warns that the :code:`defparam` statement was deprecated in IEEE 1364-2001,
   and all designs should now be using the :code:`#(...)` format to specify
   parameters.

   Defparams may be defined far from the instantiation affected by
   the defparam, affecting readability. Defparams have been formally
   deprecated since IEEE 1800-2005 25.2 and may not work in future language
   versions.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.

   Faulty example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 5

         module parameterized
            #(parameter int MY_PARAM = 0);
         endmodule
         module upper;
           defparam p0.MY_PARAM = 1;  //<--- Warning
           parameterized p0();
         endmodule

   Results in:

   .. code-block::

         %Warning-DEFPARAM: example.v:5:15: defparam is deprecated (IEEE 1800-2017 C.4.1)
                                          : ... Suggest use instantiation with #(.MY_PARAM(...etc...))

   To repair use :code:`#(.PARAMETER(...))` syntax. Repaired Example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 6

         module parameterized
            #(parameter int MY_PARAM = 0);
         endmodule
         module upper
           parameterized
              #(.MY_PARAM(1))  //<--- Repaired
              p0();
         endmodule

   Other tools with similar warnings: Verible's forbid_defparam_rule.


.. option:: DEPRECATED

   Warning that a Verilator metacomment, or configuration file command uses
   syntax that has been deprecated.  Upgrade the code to the replacement
   typically suggested by the warning message.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: DETECTARRAY

   Historical, never issued since version 3.862.

   Was an error when Verilator tried to deal with a combinatorial loop that
   could not be flattened, and which involves a datatype that Verilator
   could not handle, such as an unpacked struct or a large unpacked array.


.. option:: DIDNOTCONVERGE

   Error at simulation runtime when model did not correctly settle.

   Verilator sometimes has to evaluate combinatorial logic multiple times,
   usually around code where an :option:`UNOPTFLAT` warning was issued but
   disabled.

   Faulty example:

   .. include:: ../../docs/gen/ex_DIDNOTCONVERGE_faulty.rst

   Results in at runtime (not when Verilated):

   .. include:: ../../docs/gen/ex_DIDNOTCONVERGE_nodbg_msg.rst

   This is because the signals keep toggling even without time
   passing. Thus to prevent an infinite loop, the Verilated executable
   gives the DIDNOTCONVERGE error.

   To debug this, first, review any UNOPTFLAT warnings that were
   ignored.  Though typically, it is safe to ignore UNOPTFLAT (at a
   performance cost), at the time of issuing a UNOPTFLAT Verilator did not
   know if the logic would eventually converge and assumed it would.

   Next, run Verilator with
   :vlopt:`--prof-cfuncs -CFLAGS -DVL_DEBUG <--prof-cfuncs>`.  Rerun the
   test.  Now just before the convergence error, you should see additional
   output similar to this:

   .. include:: ../../docs/gen/ex_DIDNOTCONVERGE_msg.rst

   The CHANGE line means that the signal 'a' kept changing on the given
   filename and line number that drove the signal. Inspect the code that
   modifies these signals.  Note that if many signals are getting printed,
   then most likely, all of them are oscillating.  It may also be that,
   e.g. "a" may be oscillating, then "a" feeds signal "c", which then is
   also reported as oscillating.

   One way DIDNOTCONVERGE may occur is flops are built out of gate
   primitives. Verilator does not support building flops or latches out of
   gate primitives, and any such code must change to use behavioral
   constructs (e.g. always_ff and always_latch).

   Another way DIDNOTCONVERGE may occur is if # delays are used to generate
   clocks if Verilator is run with :vlopt:`--no-timing`. In this mode,
   Verilator ignores the delays and gives an :option:`ASSIGNDLY` or
   :option:`STMTDLY` warning.  If these were suppressed, due to the absence of
   the delay, the design might oscillate.

   Finally, rare, more difficult cases can be debugged like a C++ program;
   either enter :command:`gdb` and use its tracing facilities, or edit the
   generated C++ code to add appropriate prints to see what is going on.


.. option:: ENDCAPSULATED

   Warns that a class member is declared :code:`local` or
   :code:`protected`, but is being accessed from outside that class (if
   local) or a derived class (if protected).

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: ENDLABEL

   An error that a label attached to a "end"-something statement does not
   match the label attached to the block start.

   IEEE requires this error. Ignoring this warning will only suppress the
   lint check; it will simulate correctly.

   Faulty example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         module mine;
         endmodule : not_mine  //<--- Warning

   Results in:

   .. code-block::

         %Error-ENDLABEL: example.v:2:13: End label 'not_mine' does not match begin label 'mine'

   To repair, either fix the end label's name, or remove it entirely.

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         module mine;
         endmodule : mine  //<--- Repaired

   Other tools with similar warnings: Verible's mismatched-labels,
   "Begin/end block labels must match." or "Matching begin label is
   missing."


.. option:: ENUMVALUE

   An error that an enum data type value is being assigned from another data
   type that is not implicitly assignment compatible with that enumerated
   type.  IEEE requires this error, but it may be disabled.

   Faulty example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         typedef enum { ZERO } e_t;
         initial e_t en = 0;  //<--- Warning

   The ideal repair is to use the enumeration value's mnemonic:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         typedef enum { ZERO } e_t;
         initial e_t en = ZERO;  //<--- Repaired

   Alternatively use a static cast:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         typedef enum { ZERO } e_t;
         initial e_t en = e_t'(0);  //<--- Repaired


.. option:: EOFNEWLINE

   Warns that a file does not end in a newline.  POSIX defines that a line
   must end in a newline, as otherwise, for example :command:`cat` with the
   file as an argument may produce undesirable results.

   Repair by appending a newline to the end of the file.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.

   Other tools with similar warnings: Verible's posix-eof, "File must end
   with a newline."


.. option:: GENCLK

   Historical, never issued since version 5.000.

   Indicated that the specified signal was generated inside the model and
   used as a clock.


.. option:: GENUNNAMED

   Warns that a generate block was unnamed and "genblk" will be used per
   IEEE.

   The potential issue is that adding additional generate blocks will
   renumber the assigned names, which may cause eventual problems with
   synthesis constraints or other tools that depend on hierarchical paths
   remaining consistent.

   Blocks that are empty may not be reported with this warning, as no
   scopes are created for empty blocks, so there is no harm in having them
   unnamed.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         generate
            if (PARAM == 1) begin  //<--- Warning
            end

   Results in:

   .. code-block::

         %Warning-GENUNNAMED: example.v:2:9: Unnamed generate block (IEEE 1800-2017 27.6)

   To fix this assign a label (often with the naming convention prefix of
   :code:`gen_` or :code:`g_`), for example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         generate
            if (PARAM == 1) begin : gen_param_1  //<--- Repaired
            end

   Other tools with similar warnings: Verible's generate-label, "All
   generate block statements must have a label."


.. option:: HIERBLOCK

   Warns that the top module is marked as a hierarchy block by the
   :option:`/*verilator&32;hier_block*/` metacomment, which is not legal.
   This setting on the top module will be ignored.


.. option:: IFDEPTH

   Warns that if/if else statements have exceeded the depth specified with
   :vlopt:`--if-depth`, as they are likely to result in slow priority
   encoders.  Statements below unique and priority :code:`if` statements
   are ignored.  Solutions include changing the code to a case statement,
   or using a SystemVerilog :code:`unique if` or :code:`priority if`
   statement.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.


.. option:: IGNOREDRETURN

   Warns that a non-void function is being called as a task, and hence the
   return value is being ignored. IEEE requires this warning.

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 5

         function int function_being_called_as_task;
            return 1;
         endfunction

         initial function_being_called_as_task();  //<--- Warning

   Results in:

   .. code-block::

         %Warning-IGNOREDRETURN: example.v:5:9: Ignoring return value of non-void function (IEEE 1800-2017 13.4.1)

   The portable way to suppress this warning (in SystemVerilog) is to use a
   void cast, for example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 5

         function int function_being_called_as_task;
            return 1;
         endfunction

         initial void'(function_being_called_as_task());  //<--- Repaired

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: IMPERFECTSCH

   Historical, never issued since version 5.000.

   Warned that the scheduling of the model is not perfect, and some manual
   code edits may result in faster performance.  This warning defaulted to
   off, was not part of :vlopt:`-Wall`, and had to be turned on explicitly
   before the top module statement was processed.


.. option:: IMPLICIT

   .. TODO better example

   Warns that a wire is being implicitly declared (it is a single-bit wide
   output from a sub-module.)  While legal in Verilog, implicit
   declarations only work for single-bit wide signals (not buses), do not
   allow using a signal before it is implicitly declared by an instance,
   and can lead to dangling nets.  A better option is the
   :code:`/*AUTOWIRE*/` feature of Verilog-Mode for Emacs, available from
   `https://www.veripool.org/verilog-mode
   <https://www.veripool.org/verilog-mode>`_

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.

   Other tools with similar warnings: Icarus Verilog's implicit, "warning:
   implicit definition of wire '...'".


.. option:: IMPLICITSTATIC

   Warns that the lifetime of a task or a function was not provided and so
   was implicitly set to static. The warning is suppressed when no
   variables inside the task or a function are assigned to.

   This is a warning because the static default differs from C++, differs
   from class member function/tasks.  Static is a more dangerous default
   then automatic as static prevents the function from being reentrant,
   which may be a source of bugs, and/or performance issues.

   If the function is in a module, and does not require static behavior,
   change it to "function automatic".

   If the function is in a module, and requires static behavior, change it
   to "function static".

   If the function is in a package, it defaults to static, and label the
   function's variables as static.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: IMPORTSTAR

   .. TODO better example

   Warns that an :code:`import {package}::*` statement is in $unit
   scope. This causes the imported symbols to pollute the global namespace,
   defeating much of the purpose of having a package. Generally,
   :code:`import ::*` should only be used inside a lower scope, such as a
   package or module.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.


.. option:: IMPURE

   .. TODO better example

   Warns that a task or function that has been marked with a
   :option:`/*verilator&32;no_inline_task*/` metacomment, but it references
   variables that are not local to the task, and Verilator cannot schedule
   these variables correctly.

   Ignoring this warning may make Verilator simulations differ from other
   simulators.


.. option:: INCABSPATH

   .. TODO better example

   Warns that an "\`include" filename specifies an absolute path.  This
   means the code will not work on any other system with a different file
   system layout.  Instead of using absolute paths, relative paths
   (preferably without any directory specified) should be used,
   and +incdir used on the command line to specify the top include source
   directories.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.


.. option:: INFINITELOOP

   .. TODO better example

   Warns that a :code:`while` or :code:`for` statement has a condition that
   is always true, and thus results in an infinite loop if the statement
   ever executes.

   This might be unintended behavior if Verilator is run with
   :vlopt:`--no-timing` and the loop body contains statements that would make
   time pass otherwise.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly (i.e. hang due to the infinite loop).


.. option:: INITIALDLY

   .. TODO better example

   Warns that the code has a delayed assignment inside of an :code:`initial`
   or :code:`final` block.  If this message is suppressed, Verilator will
   convert this to a non-delayed assignment.  See also :option:`COMBDLY`.

   Ignoring this warning may make Verilator simulations differ from other
   simulators.


.. option:: INSECURE

   Warns that the combination of selected options may defeat the
   attempt to protect/obscure identifiers or hide information in the model.
   Correct the options provided, or inspect the output code to see if the
   information exposed is acceptable.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: LATCH

   .. TODO better example

   Warns that a signal is not assigned in all control paths of a
   combinational always block, resulting in the inference of a latch. For
   intentional latches, consider using the always_latch (SystemVerilog)
   keyword instead.  The warning may be disabled with a lint_off pragma
   around the always block.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.

.. option:: LIFETIME

   Error when a variable is referenced in a process that can outlive the process
   in which it was declared. This can happen when using 'fork..join_none' or
   'fork..join_any' blocks, which spawn process that can outlive their parents.
   This error occurs only when Verilator can't replace the reference with a
   reference to copy of this variable, local to the forked process. For example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 3

         task foo(int local_var);
            fork
               #10 local_var++;
               #20 $display("local_var = %d", local_var);
            join_none
         endtask

   In the example above 'local_var' exists only within scope of 'foo', once foo
   finishes, the stack frame containing 'i' gets removed. However, the process
   forked from foo continues, as it contains a delay. After 10 units of time
   pass, this process attempts to modify 'local_var'. However, this variable no
   longer exits. It can't be made local to the forked process upon spawning, because
   it's modified and can be referenced somewhere else, for example in the other
   forked process, that was delayed by 20 units of time in this example. Thus,
   there's no viable stack allocation for it.

   In order to fix it, if the intent is not to share the variable's state outside
   of the process, then create a local copy of the variable.

   For example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 4

         task foo(int local_var);
            fork
               #10 begin
                  int forked_var = local_var;
                  forked_var++;
               end
               #20 begin
                  // Note that we are going to print the original value here,
                  // as `forked_var`is a local copy that was initialized while
                  // `foo` was still alive.
                  int forked_var = local_var;
                  $display("forked_var = %d", forked_var)
               end
            join_none
         endtask

   If you need to share its state, another strategy is to ensure it's allocated
   statically:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 1

         int static_var;

         task foo();
            fork
               #10 static_var++;
               #20 $display("static_var = %d", static_var);
            join_none
         endtask

   However, if you need to be able to instantiate at runtime, the solution would be to
   wrap it in an object, since the forked process can hold a reference to that object
   and ensure that the variable stays alive this way:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         class Wrapper;
            int m_var;

            // Here we implicitly hold a reference to `this`
            task foo();
               fork
                  #10 m_var++;
                  #20 $display("this.m_var = %d", m_var);
               join_none
            endtask
         endclass

         // Here we explicitly hold a handle to an object
         task bar(Wrapper wrapper);
            fork
               #10 wrapper.m_var++;
               #20 $display("wrapper.m_var = %d", wrapper.m_var);
            join_none
         endtask

.. option:: LITENDIAN

   .. TODO better example

   The naming of this warning is in contradiction with the common
   interpretation of little endian. It was therefore renamed to
   :option:`ASCRANGE`. While :option:`LITENDIAN` remains for
   backwards compatibility, new projects should use :option:`ASCRANGE`.


.. option:: MINTYPMAX

   .. code-block:: sv

         #(3:5:8) clk = ~clk;

   Warns that minimum, typical, and maximum delay expressions are currently
   unsupported. Verilator uses only the typical delay value.


.. option:: MISINDENT

   Warns that the indentation of a statement is misleading, suggesting the
   statement is part of a previous :code:`if` or :code:`while` block while
   it is not.

   Verilator suppresses this check when there is an inconsistent mix of
   spaces and tabs, as it cannot ensure the width of tabs.  Verilator also
   ignores blocks with :code:`begin`/:code:`end`, as the :code:`end`
   visually indicates the earlier statement's end.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.

   For example

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 3

         if (something)
            statement_in_if;
            statement_not_in_if;  //<--- Warning

   Results in:

   .. code-block::

         %Warning-MISINDENT: example.v:3:9: Misleading indentation

   To fix this repair the indentation to match the correct earlier
   statement, for example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 3

         if (something)
            statement_in_if;
         statement_not_in_if;  //<--- Repaired

   Other tools with similar warnings: GCC -Wmisleading-indentation,
   clang-tidy readability-misleading-indentation.


.. option:: MODDUP

   .. TODO better example

   Warns that a module has multiple definitions.  Generally, this indicates
   a coding error, or a mistake in a library file, and it's good practice
   to have one module per file (and only put each file once on the command
   line) to avoid these issues.  For some gate level netlists duplicates
   are sometimes unavoidable, and MODDUP should be disabled.

   Ignoring this warning will cause the more recent module definition to be
   discarded.


.. option:: MULTIDRIVEN

   Warns that the specified signal comes from multiple :code:`always`
   blocks, each with different clocking. This warning does not look at
   individual bits (see the example below).

   This is considered bad style, as the consumer of a given signal may be
   unaware of the inconsistent clocking, causing clock domain crossing
   or timing bugs.

   Faulty example:

   .. include:: ../../docs/gen/ex_MULTIDRIVEN_faulty.rst

   Results in:

   .. include:: ../../docs/gen/ex_MULTIDRIVEN_msg.rst

   Ignoring this warning will only slow simulations; it will simulate
   correctly.  It may, however, cause longer simulation runtimes due to
   reduced optimizations.


.. option:: MULTITOP

   .. TODO better example

   Warns that multiple top-level modules are not instantiated by any other
   module, and both modules were put on the command line (not in a
   library). Three likely cases:

   1. A single module is intended to be the top. This warning then occurs
   because some low-level instance is being read in but is not needed as
   part of the design.  The best solution for this situation is to ensure
   that only the top module is put on the command line without any flags,
   and all remaining library files are read in as libraries with
   :vlopt:`-v`, or are automatically resolved by having filenames that
   match the module names.

   2. A single module is intended to be the top, the name of it is known,
   and all other modules should be ignored if not part of the design.  The
   best solution is to use the :vlopt:`--top` option to specify the top
   module's name. All other modules that are not part of the design will be
   for the most part, ignored (they must be clean in syntax, and their
   contents will be removed as part of the Verilog module elaboration
   process.)

   3. Multiple modules are intended to be design tops, e.g., when linting a
   library file.  As multiple modules are desired, disable the MULTITOP
   warning.  All input/outputs will go uniquely to each module, with any
   conflicting and identical signal names being made unique by adding a
   prefix based on the top module name followed by __02E (a
   Verilator-encoded ASCII ".").  This renaming is done even if the two
   modules' signals seem identical, e.g., multiple modules with a "clk"
   input.


.. option:: NEEDTIMINGOPT

   Error when a timing-related construct, such as an event control or delay,
   has been encountered, without specifying how Verilator should handle it
   (neither :vlopt:`--timing` nor :vlopt:`--no-timing` option was provided).


.. option:: NEWERSTD

   Warns that a feature requires a newer standard of Verilog or SystemVerilog
   than the one specified by the :vlopt:`--language` option. For example, unsized
   unbased literals (`'0`, `'1`, `'z`, `'x`) require 1800-2005 or later.

   To avoid this warning, use a Verilog or SystemVerilog standard that
   supports the feature. Alternatively, modify your code to use a different
   syntax that is supported by the Verilog/SystemVerilog standard specified
   by the :vlopt:`--language` option.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: NOLATCH

   .. TODO better example

   Warns that no latch was detected in an always_latch block. The warning
   may be disabled with a lint_off pragma around the always block, but
   recoding using a regular always may be more appropriate.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: NOTIMING

   Error when a timing-related construct that requires :vlopt:`--timing` has
   been encountered. Issued only if Verilator is run with the
   :vlopt:`--no-timing` option.


.. option:: NULLPORT

   Warns that a null port was detected in the module definition port
   list. Null ports are empty placeholders, i.e., either one or more commas
   at the beginning or the end of a module port list, or two or more
   consecutive commas in the middle of a module port list. A null port
   cannot be accessed within the module, but when instantiating the module
   by port order, it is treated like a regular port, and any wire connected
   to it is left unconnected. For example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

       module a
          (a_named_port, );  //<--- Warning

   This is considered a warning because null ports are rarely used, and is
   commonly the result of a typing error, such as a dangling comma at the
   end of a port list.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.

.. option:: PINCONNECTEMPTY

   .. TODO better example

   Warns that an instance has a pin that is connected to
   :code:`.pin_name()`, e.g., not another signal, but with an explicit
   mention of the pin.  It may be desirable to disable PINCONNECTEMPTY, as
   this indicates the intention to have a no-connect.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.


.. option:: PINMISSING

   .. TODO better example

   Warns that a module has a pin that is not mentioned in an instance.  If
   a pin is not missing it should still be specified on the instance
   declaration with an empty connection using :code:`(.pin_name())`.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.

   Other tools with similar warnings: Icarus Verilog's portbind, "warning:
   Instantiating module ... with dangling input port (...)". Slang's
   unconnected-port, "port '...' has no connection".


.. option:: PINNOCONNECT

   .. TODO better example

   Warns that an instance has a pin that is not connected to another
   signal.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.


.. option:: PINNOTFOUND

   Warns that an instance port or parameter was not found in the module
   being instantiated. Note that Verilator raises these errors also on
   instances that should be disabled by generate/if/endgenerate constructs:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 5-6

       module a;
         localparam A=1;
         generate
            if (A==0) begin
               b b_inst1 (.x(1'b0));  //<--- error nonexistent port
               b #(.PX(1'b0)) b_inst2 (); //<--- error nonexistent parameter
            end
          endgenerate
       endmodule

       module b;
       endmodule

   In the example above, b is instantiated with a port named x, but module
   b has no such port. In the following line, b is instantiated with a
   nonexistent PX parameter. Technically, this code is incorrect because of
   this, but other tools may ignore it because module b is not instantiated
   due to the generate/if condition being false.

   This error may be disabled with a lint_off PINNOTFOUND metacomment.


.. option:: PORTSHORT

   Warns that an output port is connected to a constant.

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 5-6

       module a;
         sub sub
            (.out(1'b1));  //<--- error PORTSHORT
       endmodule

       module sub (output out);
         assign out = '1;
       endmodule

   In the example above, out is an output but is connected to a constant,
   implying it is an input.

   This error may be disabled with a lint_off PORTSHORT metacomment.


.. option:: PKGNODECL

   .. TODO better example

   An error that a package/class appears to have been referenced that has not
   yet been declared.  According to IEEE 1800-2017 26.3, all packages must
   be declared before being used.


.. option:: PROCASSWIRE

   .. TODO better example

   An error that a procedural assignment is setting a wire. According to IEEE,
   a var/reg must be used as the target of procedural assignments.


.. option:: PROFOUTOFDATE

   Warns that threads were scheduled using estimated costs, even though
   that data was provided from profile-guided optimization (see
   :ref:`Thread PGO`) as fed into Verilator using the
   :option:`profile_data` configuration file option.  This usually
   indicates that the profile data was generated from a different Verilog
   source code than Verilator is currently running against.

   It is recommended to create new profiling data, then rerun Verilator
   with the same input source files and that new profiling data.

   Ignoring this warning may only slow simulations; it will simulate
   correctly.


.. option:: PROTECTED

   Warning that a 'pragma protected' section was encountered. The code
   inside the protected region will be partly checked for correctness but is
   otherwise ignored.

   Suppressing the warning may make Verilator differ from a simulator that
   accepts the protected code.


.. option:: RANDC

   Historical, never issued since version 5.018, when :code:`randc` became
   fully supported.

   Warned that the :code:`randc` keyword was unsupported and was converted
   to :code:`rand`.


.. option:: REALCVT

   Warns that a real number is being implicitly rounded to an integer, with
   possible loss of precision.

   Faulty example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         int i;
         i = 2.3;  //<--- Warning

   Results in:

   .. code-block::

         %Warning-REALCVT: example.v:2:5: Implicit conversion of real to integer

   If the code is correct, the portable way to suppress the warning is to
   add a cast.  This will express the intent and should avoid future
   warnings on any linting tool.

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         int i;
         i = int'(2.3);  //<--- Repaired


.. option:: REDEFMACRO

   Warns that the code has redefined the same macro with a different value,
   for example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 3

         `define DUP def1
         //...
         `define DUP def2  //<--- Warning

   Results in:

   .. code-block::

         %Warning-REDEFMACRO: example.v:3:20: Redefining existing define: 'DUP', with different value: 'def1'
                              example.v:1:20: ... Location of previous definition, with value: 'def2'

   The best solution is to use a different name for the second macro.  If
   this is infeasible, add an undef to indicate that the code overriding the
   value. This will express the intent and should avoid future warnings on
   any linting tool:

   .. code-block:: sv

         `define DUP def1
         //...
         `undef DUP  //<--- Repaired
         `define DUP def2

   Other tools with similar warnings: Icarus Verilog's macro-redefinition,
   "warning: redefinition of macro ... from value '...' to '...'".  Yosys's
   "Duplicate macro arguments with name".


.. option:: RISEFALLDLY

   .. code-block:: sv

         and #(1,2,3) AND (out, a, b);

   Warns that rising, falling, and turn-off delays are currently unsupported.
   The first (rising) delay is used for all cases.


.. option:: SELRANGE

   Warns that a selection index will go out of bounds.

   Faulty example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 2

         wire vec[6:0];
         initial out = vec[7];  //<--- Warning (there is no [7])

   Verilator will assume zero for this value instead of X.  Note that in
   some cases, this warning may be false, when a condition upstream or
   downstream of the access means the access out of bounds will never
   execute or be used.

   Repaired example:

   .. code-block:: sv
      :linenos:

         wire vec[6:0];
         initial begin
            index = 7;
            ...
            if (index < 7) out = vec[index];  // Never will use vec[7]

   Other tools with similar warnings: Icarus Verilog's select-range,
   "warning: ... [...] is selecting before vector" or "is selecting before
   vector".


.. option:: SHORTREAL

   Warns that Verilator does not support :code:`shortreal`, and they will be
   automatically promoted to :code:`real`.

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 1

         shortreal sig;  //<--- Warning

   The recommendation is to replace any :code:`shortreal` in the code with
   :code:`real`, as :code:`shortreal` is not widely supported across
   industry tools.

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 1

         real sig;  //<--- Repaired

   Ignoring this warning may make Verilator simulations differ from other
   simulators if the increased precision of :code:`real` affects the
   modeled values, or DPI calls.


.. option:: SPLITVAR

   Warns that a variable with a :option:`/*verilator&32;split_var*/`
   metacomment was not split.  Some possible reasons for this are:

   * The datatype of the variable is not supported for splitting. (e.g., is
     a real).

   * The access pattern of the variable can not be determined
     statically. (e.g., is accessed as a memory).

   * The index of the array exceeds the array size.

   * The variable is accessed from outside using a dotted reference.
     (e.g. :code:`top.instance0.variable0 = 1`).

   * The variable is not declared in a module, but in a package or an
     interface.

   * The variable is a parameter, localparam, genvar, or queue.

   * The variable is tristate or bidirectional. (e.g., :code:`inout`).


.. option:: STATICVAR

   Warns that a static variable declared in a loop with declaration assignment
   was converted to automatic. Often such variables were intended to
   instead be declared "automatic".

   Ignoring this warning may make Verilator differ from other simulators,
   which will treat the variable as static. Verilator may in future versions also
   treat the variable as static.


.. option:: STMTDLY

   Warns that the code has a statement with a delayed time in front of it.

   Ignoring this warning may make Verilator simulations differ from other
   simulators.

   Faulty example:

   .. include:: ../../docs/gen/ex_STMTDLY_faulty.rst

   Results in:

   .. include:: ../../docs/gen/ex_STMTDLY_msg.rst

   This warning is issued only if Verilator is run with :vlopt:`--no-timing`.
   All delays on statements are ignored in this mode.  In many cases ignoring a
   delay might be harmless, but if the delayed statement is, as in this
   example, used to cause some important action later, it might be an
   important difference.

   Some possible workarounds:

   * Move the delayed statement into the C++ wrapper file, where the
     stimulus and clock generation can be done in C++.

   * Convert the statement into an FSM, or other statement that tests
     against $time.

   * Run Verilator with :vlopt:`--timing`.


.. option:: SYMRSVDWORD

   Warning that a symbol matches a C++ reserved word, and using this as a
   symbol name would result in odd C++ compiler errors.  You may disable
   this warning, but Verilator will rename the symbol to avoid conflict.


.. option:: SYNCASYNCNET

   .. TODO better example

   Warns that the specified net is used in at least two different always
   statements with posedge/negedges (i.e., a flop).  One usage has the
   signal in the sensitivity list and body, probably as an async reset, and
   the other has the signal only in the body, probably as a sync reset.
   Mixing sync and async resets is usually a mistake.  The warning may be
   disabled with a lint_off pragma around the net or flopped block.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.


.. option:: TASKNSVAR

   Error when a call to a task or function has an inout from that task tied
   to a non-simple signal.  Instead, connect the task output to a temporary
   signal of the appropriate width, and use that signal to set the
   appropriate expression as the next statement.  For example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 4

         task foo(inout sig); ... endtask
         // ...
         always @* begin
              foo(bus_we_select_from[2]);  // Will get TASKNSVAR error
         end

   Change this to:

   .. code-block:: sv

         task foo(inout sig); ... endtask
         // ...
         reg foo_temp_out;
         always @* begin
            foo(foo_temp_out);
            bus_we_select_from[2] = foo_temp_out;
         end

   Verilator doesn't do this conversion for you, as some more complicated
   cases would result in simulator mismatches.


.. option:: TICKCOUNT

   Warns that the number of ticks to delay a $past variable is greater
   than 10.  At present, Verilator effectively creates a flop for each
   delayed signal, and as such, any large counts may lead to large design
   size increases.

   Ignoring this warning will only slow simulations; it will simulate
   correctly.


.. option:: TIMESCALEMOD

   Warns that "\`timescale" is used in some but not all modules.

   This may be disabled, similar to other warnings.  Ignoring this warning
   may result in a module having an unexpected timescale.

   IEEE recommends this be an error; for that behavior, use
   :vlopt:`-Werror-TIMESCALEMOD <-Werror-\<message\>>`.

   Faulty example:

   .. code-block:: sv
      :linenos:
      :emphasize-lines: 5

         module mod1;
           sub sub();
         endmodule
         `timescale 1ns/1ns
         module sub;  //<--- Warning
         endmodule

   Results in:

   .. code-block::

         %Warning-TIMESCALEMOD: example.v:1:8: Timescale missing on this module as other modules have it (IEEE 1800-2017 3.14.2.3)

   Recommend using :vlopt:`--timescale` argument, or in front of all
   modules use:

   .. code-block:: sv

         `include "timescale.vh"

   Then in that file, set the timescale.

   Other tools with similar warnings: Icarus Verilog's timescale, "warning:
   Some design elements have no explicit time unit and/or time
   precision. This may cause confusing timing results." Slang's:
   "[WRN:PA0205] No timescale set for "..."".


.. option:: UNDRIVEN

   .. TODO better example

   Warns that the specified signal has no source.  Verilator is relatively
   liberal in the usage calculations; making a signal public, or setting
   only a single array element marks the entire signal as driven.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.

   Other tools with similar warnings: Odin's "[NETLIST] This output is
   undriven (...) and will be removed".


.. option:: UNOPT

   Historical, never issued since version 5.000.

   Warned that due to some construct, optimization of the specified signal
   or block was disabled.

   Ignoring this warning only slowed simulations; it simulated correctly.


.. option:: UNOPTFLAT

   .. TODO better example

   Warns that due to some construct, optimization of the specified signal
   is disabled.  The signal reported includes a complete scope to the
   signal; it may be only one particular usage of a multiply-instantiated
   block.  The construct should be cleaned up to improve simulation
   performance.

   Often UNOPTFLAT is caused by logic that isn't truly circular as viewed by
   synthesis, which analyzes interconnection per bit, but is circular to
   the IEEE event model which analyzes per-signal.

   Faulty example:

   .. code-block:: sv

         wire [2:0] x = {x[1:0], shift_in};

   This statement needs to be evaluated multiple times, as a change in
   :code:`shift_in` requires "x" to be computed three times before it becomes
   stable.  This is because a change in "x" requires "x" itself to change
   its value, which causes the warning.

   For significantly better performance, split this into two separate signals:

   .. code-block:: sv

         wire [2:0] xout = {x[1:0], shift_in};

   And change all receiving logic to instead receive "xout".
   Alternatively, change it to:

   .. code-block:: sv

         wire [2:0] x = {xin[1:0], shift_in};

   And change all driving logic to drive "xin" instead.

   With this change, this assignment needs to be evaluated only once.
   These sorts of changes may also speed up your traditional event-driven
   simulator, as it will result in fewer events per cycle.

   The most complicated UNOPTFLAT path we've seen was due to low bits of a
   bus generated from an always statement that consumed high bits of the
   same bus processed by another series of always blocks.  The fix is the
   same; split it into two separate signals generated from each block.

   Occasionally UNOPTFLAT may be indicated when there is a true
   circulation.  e.g., if trying to implement a flop or latch using
   individual gate primitives.  If UNOPTFLAT is suppressed, the code may
   get a DIDNOTCONVERGE error. Verilator does not support building flops or
   latches out of gate primitives, and any such code must change to use
   behavioral constructs (e.g., :code:`always_ff` and
   :code:`always_latch`).

   Another way to resolve this warning is to add a
   :option:`/*verilator&32;split_var*/` metacomment described above. This
   will cause the variable to be split internally, potentially resolving
   the conflict. If you run with :vlopt:`--report-unoptflat`, Verilator will
   suggest possible candidates for :option:`/*verilator&32;split_var*/`.

   The UNOPTFLAT warning may also occur where outputs from a block of logic
   are independent, but occur in the same always block.  To fix this, use
   the :option:`/*verilator&32;isolate_assignments*/` metacomment described
   above.

   Before version 5.000, the UNOPTFLAT warning may also have been due to
   clock enables, identified from the reported path going through a clock
   gating instance.  To fix these, the clock_enable meta comment was used.

   To assist in resolving UNOPTFLAT, the option :vlopt:`--report-unoptflat`
   can be used, which will provide suggestions for variables that can be
   split up, and a graph of all the nodes connected in the loop. See the
   Arguments section for more details.

   Ignoring this warning will only slow simulations; it will simulate
   correctly.


.. option:: UNOPTTHREADS

   .. TODO better example

   Warns that the thread scheduler could not partition the design to fill
   the requested number of threads.

   One workaround is to request fewer threads with :vlopt:`--threads`.

   Another possible workaround is to allow more MTasks in the simulation
   runtime by increasing the value of :vlopt:`--threads-max-mtasks`. More
   MTasks will result in more communication and synchronization overhead at
   simulation runtime; the scheduler attempts to minimize the number of
   MTasks for this reason.

   Ignoring this warning will only slow simulations; it will simulate
   correctly.


.. option:: UNPACKED

   Warns that unpacked structs and unions are not supported.

   Ignoring this warning will make Verilator treat the structure as packed,
   which may make Verilator simulations differ from other simulators. This
   downgrading may also result in what would typically be a legal unpacked
   struct/array inside an unpacked struct/array becoming an illegal
   unpacked struct/array inside a packed struct/array.


.. option:: UNSIGNED

   .. TODO better example

   Warns that the code is comparing an unsigned value in a way that implies
   it is signed; for example :code:`X < 0` will always be false when X is
   unsigned.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.


.. option:: UNSUPPORTED

   An error that a construct might be legal according to IEEE but is not
   currently supported by Verilator.

   A typical workaround is to rewrite the construct into a more common
   alternative language construct.

   Alternatively, check if other tools support the construct, and if so,
   please consider submitting a github pull request against the Verilator
   sources to implement the missing unsupported feature.

   This error may be ignored with :vlopt:`--bbox-unsup`, however, this will
   make the design simulate incorrectly and is only intended for lint
   usage; see the details under :vlopt:`--bbox-unsup`.


.. option:: UNUSED

   Disabling/enabling UNUSED is equivalent to disabling/enabling the
   :option:`UNUSEDGENVAR`, :option:`UNUSEDPARAM`, and
   :option:`UNUSEDSIGNAL` warnings.

   Never issued since version 5.000.  Historically warned that a variable,
   parameter, or signal was unused.

.. option:: UNUSEDGENVAR

   .. TODO better example

   Warns that the specified genvar is never used/consumed.


.. option:: UNUSEDPARAM

   .. TODO better example

   Warns that the specified parameter is never used/consumed.


.. option:: UNUSEDSIGNAL

   .. TODO better example

   Warns that the specified signal is never used/consumed.
   Verilator is relatively liberal in the usage calculations; making a signal
   public, a signal matching the :vlopt:`--unused-regexp` option (default
   "\*unused\*" or accessing only a single array element marks the entire
   signal as used.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.

   A recommended style for unused nets is to put at the bottom of a file
   code similar to the following:

   .. code-block:: sv

         wire _unused_ok = &{1'b0,
                             sig_not_used_a,
                             sig_not_used_yet_b,  // To be fixed
                             1'b0};

   The reduction AND and constant zeros mean the net will always be zero,
   so won't use simulation runtime.  The redundant leading and trailing
   zeros avoid syntax errors if there are no signals between them.  The
   magic name "unused" (controlled by the :vlopt:`--unused-regexp` option)
   is recognized by Verilator and suppresses warnings; if using other lint
   tools, either teach the tool to ignore signals with "unused" in the
   name, or put the appropriate lint_off around the wire.  Having unused
   signals in one place makes it easy to find what is unused and reduces
   the number of lint_off pragmas, reducing bugs.


.. option:: USERERROR

   A SystemVerilog elaboration-time assertion error was executed.
   IEEE 1800-2017 20.11 requires this error.

   Faulty example:

   .. include:: ../../docs/gen/ex_USERERROR_faulty.rst

   Results in:

   .. include:: ../../docs/gen/ex_USERERROR_msg.rst

   To resolve, examine the code and rectify the cause of the error.


.. option:: USERFATAL

   A SystemVerilog elaboration-time assertion fatal was executed.
   IEEE 1800-2017 20.11 requires this error.

   Faulty example:

   .. include:: ../../docs/gen/ex_USERFATAL_faulty.rst

   Results in:

   .. include:: ../../docs/gen/ex_USERFATAL_msg.rst

   To resolve, examine the code and rectify the cause of the fatal.


.. option:: USERINFO

   A SystemVerilog elaboration-time assertion print was executed.  This is
   not an error or warning, and IEEE 1800-2017 20.11 requires this
   behavior.

   Example:

   .. include:: ../../docs/gen/ex_USERINFO_faulty.rst

   Results in:

   .. include:: ../../docs/gen/ex_USERINFO_msg.rst


.. option:: USERWARN

   A SystemVerilog elaboration-time assertion warning was executed.
   IEEE 1800-2017 20.11 requires this warning.

   Faulty example:

   .. include:: ../../docs/gen/ex_USERWARN_faulty.rst

   Results in:

   .. include:: ../../docs/gen/ex_USERWARN_msg.rst

   To resolve, examine the code and rectify the cause of the error.


.. option:: VARHIDDEN

   Warns that a task, function, or begin/end block is declaring a variable
   by the same name as a variable in the upper-level module or begin/end
   block (thus hiding the upper variable from being able to be used.)
   Rename the variable to avoid confusion when reading the code.

   Disabled by default as this is a code-style warning; it will simulate
   correctly.

   Faulty example:

   .. include:: ../../docs/gen/ex_VARHIDDEN_faulty.rst

   Results in:

   .. include:: ../../docs/gen/ex_VARHIDDEN_msg.rst

   To resolve this, rename the variable to an unique name.


.. option:: WAITCONST

   .. code-block:: sv

         wait(1);  // Blocks forever

   Warns that a `wait` statement awaits a constant condition, which means it
   either blocks forever or never blocks.

   As a special case `wait(0)` with the literal constant `0` (as opposed to
   something that elaborates to zero), does not warn, as it is presumed the
   code is making the intent clear.


.. option:: WIDTH

   Warns that based on the width rules of Verilog:

   * Two operands have different widths, e.g., adding a 2-bit and 5-bit
     number.

   * A part select has a different size then needed to index into the
     packed or unpacked array, etc.

   Verilator attempts to track the minimum width of unsized constants
   and will suppress the warning when the minimum width is appropriate to
   fit the required size.

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.

   The recommendation is to fix these issues by:

   * Resize the variable or constant to match the needed size for the
     expression.  E.g., :code:`2'd2` instead of :code:`3'd2`.

   * Using :code:`'0` or :code:`'1`, which automatically resize in an
     expression.

   * Using part selects to narrow a variable; e.g., :code:`too_wide[1:0]`.

   * Using concatenate to widen a variable; e.g., :code:`{1'b1, too_narrow}`.

   * Using cast to resize a variable; e.g., :code:`23'(wrong_sized)`.

   For example, this is a missized index:

   .. include:: ../../docs/gen/ex_WIDTHEXPAND_1_faulty.rst

   Results in a WIDTHEXPAND warning:

   .. include:: ../../docs/gen/ex_WIDTHEXPAND_1_msg.rst

   One possible fix:

   .. include:: ../../docs/gen/ex_WIDTHEXPAND_1_fixed.rst


.. option:: WIDTHTRUNC

   A more granular WIDTH warning, for when a value is truncated.

.. option:: WIDTHEXPAND

   A more granular WIDTH warning, for when a value is zero expanded.

.. option:: WIDTHXZEXPAND

   A more granular WIDTH warning, for when a value is X/Z expanded.

.. option:: WIDTHCONCAT

   Warns that based on the width rules of Verilog, a concatenate, or
   replication has an indeterminate width.  In most cases, this violates
   the Verilog rule that widths inside concatenates and replicates must be
   sized and should be fixed in the code.

   Faulty example:

   .. code-block:: sv

         wire [63:0] concat = {1, 2};

   An example where this is technically legal (though still bad form) is:

   .. code-block:: sv

         parameter PAR = 1;
         wire [63:0] concat = {PAR, PAR};

   The correct fix is to either size the 1 (:code:`32'h1`), add the
   width to the parameter definition (:code:`parameter [31:0]`), or add the
   width to the parameter usage (:code:`{PAR[31:0], PAR[31:0]}`).


.. option:: ZERODLY

   Warns that `#0` delays do not schedule the process to be resumed in the
   Inactive region. Such processes do get resumed in the same time slot
   somewhere in the Active region. Issued only if Verilator is run with the
   :vlopt:`--timing` option.
