.. SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _verilator control files:

=======================
Verilator Control Files
=======================

In addition to the command line, warnings and other features for the
:command:`verilator` command may be controlled with Verilator Control
Files, not to be confused with IEEE Configurations blocks
(`config...endconfig`). Typically named with the `.vlt` extension, what
makes it a Verilator Control File is the :option:`\`verilator_config`
directive. These files, when named `.vlt`, are read before source code
files; if this behavior is undesired, name the control file with a `.v` or
other suffix.

An example:

.. code-block:: sv

   `verilator_config
   lint_off -rule WIDTH
   lint_off -rule CASEX  -file "silly_vendor_code.v"

This disables WIDTH warnings globally, and CASEX for a specific file.

Verilator control files are fed through the normal Verilog preprocessor
prior to parsing, so "\`ifdef", "\`define", and comments may be used as if
the control file was standard Verilog code.

Note that file or line-specific control only applies to files read after
the control file. It is therefore recommended to pass the control file to
Verilator as the first file.

The grammar of control commands is as follows:

.. option:: `verilator_config

   Take the remaining text and treat it as Verilator Control File commands.
   See :ref:`Verilator Control Files`.

.. option:: clock_enable -module "<modulename>" -var "<signame>"

   Deprecated and has no effect (ignored).

   In versions before 5.000:

   Indicates that the signal is used to gate a clock, and the user takes
   responsibility for ensuring there are no races related to it.

   Same as :option:`/*verilator&32;clock_enable*/` metacomment.


   .. t_dist_docs_style ignore no_clocker

.. option:: clocker -module "<modulename>" [-function "<funcname>"] -var "<signame>"

.. option:: clocker -module "<modulename>" [-task "<taskname>"] -var "<signame>"

.. option:: no_clocker -module "<modulename>" [-function "<funcname>"] -var "<signame>"

.. option:: no_clocker -module "<modulename>" [-task "<taskname>"] -var "<signame>"

   Deprecated and has no effect (ignored).

   In versions before 5.042:

   Indicates whether the signal is used as clock or not. Verilator uses
   this information to mark the signal and any derived signals as clocker.
   See :vlopt:`--clk`.

   Same as :option:`/*verilator&32;clocker*/` metacomment.

.. option:: coverage_block_off -file "<filename>" -line <lineno>

.. option:: coverage_block_off -module "<modulename>" -block "<blockname>"

   Specifies the entire begin/end block should be ignored for coverage
   analysis purposes. It can either be specified as a named block or as a
   filename and line number.

   Same as :option:`/*verilator&32;coverage_block_off*/` metacomment.

.. option:: coverage_off [-file "<filename>" [-lines <line> [ - <line> ]]]

.. option:: coverage_on  [-file "<filename>" [-lines <line> [ - <line> ]]]

   Enable/disable coverage for the specified filename (or wildcard with
   '\*' or '?', or all files if omitted) and range of line numbers (or all
   lines if omitted). Often used to ignore an entire module for coverage
   analysis purposes.

.. option:: forceable -module "<modulename>" -var "<signame>"

   Generate public `<signame>__VforceEn` and `<signame>__VforceVal` signals
   that can force/release a signal from C++ code. The force control
   signals are created as :option:`public_flat` signals.

   Same as :option:`/*verilator&32;forceable*/` metacomment.

.. option:: full_case -file "<filename>" -lines <lineno>

   Same as ``//synthesis full_case``. When these synthesis directives
   are discovered, Verilator will either formally prove the directive to be
   true, or, failing that, will insert the appropriate code to detect
   failing cases at simulation runtime and print an "Assertion failed"
   error message.

.. option:: hier_block -module "<modulename>"

   Specifies that the module is an unit of hierarchical Verilation. Note
   that the setting is ignored unless the :vlopt:`--hierarchical` option is
   specified. See :ref:`Hierarchical Verilation`.

.. option:: hier_params -module "<modulename>"

   Specifies that the module contains parameters a :vlopt:`--hierarchical` block. This option
   is used internally to specify parameters for deparametrized hier block instances.
   This option should not be used directly.
   See :ref:`Hierarchical Verilation`.

.. option:: hier_workers -hier-dpi "<function_name>" -workers <worker_count>

   Specifies how many threads need to be used for scheduling hierarchical DPI
   tasks. This data is inserted internally during :vlopt:`--hierarchical`,
   based on value specified in `hier_workers -module`. This option
   should not be used directly. See :ref:`Hierarchical Verilation`.

.. option:: hier_workers -module "<module_name>" -workers <worker_count>

   Specifies how many threads need to be used for scheduling given module with
   :option:`/*verilator&32;hier_block*/` metacomment. This number needs to be
   smaller than :vlopt:`--threads` to fit in a thread schedule.
   See :ref:`Hierarchical Verilation`.

.. option:: inline -module "<modulename>"

   Specifies the module may be inlined into any modules that use this
   module. Same as :option:`/*verilator&32;inline_module*/` metacomment.

   .. t_dist_docs_style ignore no_inline

.. option:: no_inline -module "<modulename>"

   Specifies the module should not be inlined into any modules that use
   this module. Same as :option:`/*verilator&32;no_inline_module*/`
   metacomment.

.. option:: no_inline [-module "<modulename>"] -function "<funcname>"

.. option:: no_inline [-module "<modulename>"] -task "<taskname>"

   Specify the function or task should not be inlined into where it is
   used. This may reduce the size of the final executable when a task is
   used a very large number of times. For this flag to work, the task and
   tasks below it must be pure; they cannot reference any variables outside
   the task itself.

   Same as :option:`/*verilator&32;no_inline_task*/` metacomment.

.. option:: isolate_assignments -module "<modulename>" -function "<fname>"

.. option:: isolate_assignments -module "<modulename>" [-function "<funcname>"] -var "<signame>"

.. option:: isolate_assignments -module "<modulename>" [-task "<taskname>"] -var "<signame>"

   Used to indicate that the assignments to this signal in any blocks
   should be isolated into new blocks. Same as
   :option:`/*verilator&32;isolate_assignments*/` metacomment.

.. option:: lint_off [-rule <message>] [-file "<filename>" [-lines <line> [ - <line>]]]

.. option:: lint_off [-rule <message>] [-file "<filename>"] [-contents "<wildcard>"] [-match "<wildcard>"]

.. option:: lint_on  [-rule <message>] [-file "<filename>" [-lines <line> [ - <line>]]]

   Enable/disables the specified lint warning, in the specified filename
   (or wildcard with '\*' or '?', or all files if omitted) and range of
   line numbers (or all lines if omitted).

   If the ``-rule`` is omitted, all lint warnings (see list in
   :vlopt:`-Wno-lint`) are enabled/disabled.

   If ``-contents`` is provided, the input files must contain the given
   wildcard (with '\*' or '?'), and are waived in case they match, provided
   the ``-rule``, ``-file``, and ``-contents`` also match. The wildcard
   should be designed to match a single line; it is unspecified if the
   wildcard is allowed to match across multiple lines. The input contents
   does not include :vlopt:`--std <--no-std>` standard files, nor control
   files (with ``verilator_config``). Typical use for this is to match a
   version number present in the Verilog sources, so that the waiver will
   only apply to that version of the sources.

   If ``-match`` is provided, the linter warnings are matched against the
   given wildcard (with '\*' or '?'), and are waived in case they match,
   provided the ``-rule``, ``-file``, and ``-contents`` also match. The
   wildcard is compared across the entire multi-line message; see
   :vlopt:`--waiver-multiline`.

   When there are overlapping conflicting lint_on/lint_off directives, they
   are resolved in the following priority order:

   * All lint_on/lint_off without a ``-file``, or with a ``-file "\*"``,
     are processed in order of parsing.
   * All lint_on/lint_off with ``-file "non-\*"`` are processed in order of
     parsing.
   * All lint_off with ``--match`` in order of parsing.

   If a warning is disabled with lint_off, it will not be printed, even if
   the source contains a lint_on metacomment. The control file directives
   and metacomments are interpreted separately and do not interact. A
   warning is emitted only if not disabled either in a control file or via
   metacomments.

   Before version 4.026, ``-rule`` was named ``-msg``, and
   ``-msg`` remained a deprecated alias until Version 5.000.

.. option:: parallel_case -file "<filename>" -lines <lineno>

   Same as ``//synthesis parallel_case``. When these synthesis
   directives are discovered, Verilator will either formally prove the
   directive to be true, or, failing that, will insert the appropriate code
   to detect failing cases at simulation runtime and print an "Assertion
   failed" error message.

.. option:: profile_data -hier-dpi "<function_name>" -cost <cost_value>

   Internal profiling data inserted during :vlopt:`--hierarchical`; specifies
   execution cost of a hierarchical DPI wrappers for modules with
   :option:`/*verilator&32;hier_block*/` metacomment. See
   :ref:`Hierarchical Verilation`.

.. option:: profile_data -mtask "<mtask_hash>" -cost <cost_value>

   Feeds profile-guided optimization data into the Verilator algorithms in
   order to improve model runtime performance. This option is not expected
   to be used by users directly. See :ref:`Thread PGO`.

.. option:: public [-module "<modulename>"] [-task/-function "<taskname>"] [-var "<signame>"]

.. option:: public_flat [-module "<modulename>"] [-task/-function "<taskname>"] [(-param | -port | -var) "<signame>"]

.. option:: public_flat_rd [-module "<modulename>"] [-task/-function "<taskname>"] [(-param | -port | -var) "<signame>"]

.. option:: public_flat_rw [-module "<modulename>"] [-task/-function "<taskname>"] [(-param | -port | -var) "<signame>"] ["@(edge)"]

   Sets the specified signal to be public. Same as
   :option:`/*verilator&32;public*/` or
   :option:`/*verilator&32;public_flat*/`, etc., metacomments. See also
   :ref:`VPI Example`.

   Using ``-port`` only selects matching ports, ``-param`` matches
   parameters and localparams, and ``-var`` matches any signal (including
   ports, parameters, and regular variables or nets). In all three, the
   following ``<signame>`` can contain ``*`` and ``?`` wildcard
   characters that match any substring or any single character respectively.

.. option:: sc_biguint -module "<modulename>" -var "<signame>"

   Sets the input/output signal to be of ``sc_biguint<{width}>`` type.
   This metacomment works for signals of any width.
   Same as :option:`/*verilator&32;sc_biguint*/` metacomment.

.. option:: sc_bv -module "<modulename>" -var "<signame>"

   Sets the port to be of ``sc_bv<{width}>`` type, instead of bool,
   uint32_t, or uint64_t. Same as :option:`/*verilator&32;sc_bv*/`
   metacomment.

.. option:: sformat [-module "<modulename>"] [-function "<funcname>"] -var "<signame>"

.. option:: sformat [-module "<modulename>"] [-task "<taskname>"] -var "<signame>"

   Must be applied to the final argument of type ``input string`` of a
   function or task to indicate that the function or task should pass all
   remaining arguments through $sformatf. This allows the creation of DPI
   functions with $display-like behavior. See the
   :file:`test_regress/t/t_dpi_display.v` file for an example.

   Same as :option:`/*verilator&32;sformat*/` metacomment.

.. option:: split_var [-module "<modulename>"] [-function "<funcname>"] -var "<varname>"

.. option:: split_var [-module "<modulename>"] [-task "<taskname>"] -var "<varname>"

   Break the variable into multiple pieces typically to resolve UNOPTFLAT
   performance issues. Typically the variables to attach this to are
   recommended by Verilator itself; see :option:`UNOPTFLAT`.

   Same as :option:`/*verilator&32;split_var*/` metacomment.

.. option:: timing_off [-file "<filename>" [-lines <line> [ - <line>]]]

.. option:: timing_on  [-file "<filename>" [-lines <line> [ - <line>]]]

   Enables/disables timing constructs for the specified file and lines.
   When disabled, all timing control constructs in the specified source
   code locations are ignored the same way as with the
   :option:`--no-timing`, and code:`fork`/``join*`` blocks are
   converted into ``begin``/``end`` blocks.

   Similar to :option:`/*verilator&32;timing_on*/`,
   :option:`/*verilator&32;timing_off*/` meta-comments, but interpreted
   independently. If either a control file, or meta-comments disable timing
   constructs, they will be disabled.

   .. t_dist_docs_style ignore tracing_on

.. option:: tracing_off [-file "<filename>" [-lines <line> [ - <line> ]]]

.. option:: tracing_on  [-file "<filename>" [-lines <line> [ - <line> ]]]

.. option:: tracing_off [-scope "<scopename>" [-levels <levels> ]]

.. option:: tracing_on  [-scope "<scopename>" [-levels <levels> ]]

   Enable/disable waveform tracing for all future signals declared in
   all files.

   With ``-file``, enable/disable waveform tracing in the specified
   filename (or wildcard with '\*' or '?'), and ``-line`` range of line
   numbers (or all lines if omitted).

   For tracing_off with ``-file``, instances below any module in the
   files/ranges specified will also not be traced. To overcome this
   feature, use tracing_on on the upper module declaration and on any
   cells, or use the ``-scope`` flavor of the command.

   With ``-scope`` enable/disable waveform tracing for the specified scope
   (or wildcard with '\*' or '?'), and optional ``--levels`` number of
   levels below. These controls only operate after other
   file/line/module-based controls have indicated the signal should be
   traced. Matching is performed on the shortest prefix first, such that
   ``tracing_on -scope "a.b" tracing_off -scope "a"`` will turn it on for
   "a.b" and off for everything else "a.*".

   With ``-levels`` (used with ``-scope``), the number of levels below that
   scope which the rule is to match, where 0 means all levels below, 1 the
   exact level as the provided scope, and 2 means an additional level of
   children below the provided scope, etc.

.. option:: verilator_lib -module "<modulename>"

   Internal use only. Marks the specified module as being a stub for a library
   created by :vlopt:`--lib-create` (including when created with
   :vlopt:`--hierarchical`). Required for special internal processing.
