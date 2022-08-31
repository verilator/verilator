.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

verilator Arguments
===================

The following are the arguments that may be passed to the "verilator"
executable.

Summary:

   .. include:: ../_build/gen/args_verilator.rst


.. option:: <file.v>

   Specifies the Verilog file containing the top module to be Verilated.

.. option:: <file.c/.cc/.cpp/.cxx>

   Used with :vlopt:`--exe` to specify optional C++ files to be linked in
   with the Verilog code.  The file path should either be absolute, or
   relative to where the make will be executed from, or add to your
   makefile's VPATH the appropriate directory to find the file.

   See also :vlopt:`-CFLAGS` and :vlopt:`-LDFLAGS` options, which are
   useful when the C++ files need special compiler flags.

.. option:: <file.a/.o/.so>

   Specifies optional object or library files to be linked in with the
   Verilog code, as a shorthand for :vlopt:`-LDFLAGS \<file\>
   <-LDFLAGS>`. The file path should either be absolute, or relative to
   where the make will be executed from, or add to your makefile's VPATH
   the appropriate directory to find the file.

   If any files are specified in this way, Verilator will include a make
   rule that uses these files when linking the module's executable.  This
   generally is only useful when used with the :vlopt:`--exe` option.

.. option:: +1364-1995ext+<ext>

.. option:: +1364-2001ext+<ext>

.. option:: +1364-2005ext+<ext>

.. option:: +1800-2005ext+<ext>

.. option:: +1800-2009ext+<ext>

.. option:: +1800-2012ext+<ext>

.. option:: +1800-2017ext+<ext>

   Specifies the language standard to be used with a specific filename
   extension, <ext>.

   For compatibility with other simulators, see also the synonyms
   :vlopt:`+verilog1995ext+\<ext\>`, :vlopt:`+verilog2001ext+\<ext\>`, and
   :vlopt:`+systemverilogext+\<ext\>`.

   For any source file, the language specified by these options takes
   precedence over any language specified by the
   :vlopt:`--default-language` or :vlopt:`--language` options.

   These options take effect in the order they are encountered. Thus the
   following would use Verilog 1995 for ``a.v`` and Verilog 2001 for
   ``b.v``:

   .. code-block:: bash

        verilator ... +1364-1995ext+v a.v +1364-2001ext+v b.v

   These options are only recommended for legacy mixed language designs, as
   the preferable option is to edit the code to repair new keywords, or add
   appropriate ```begin_keywords``.

   .. note::

      ```begin_keywords`` is a SystemVerilog construct, which specifies
      *only* the set of keywords to be recognized. This also controls some
      error messages that vary between language standards.  Note at present
      Verilator tends to be overly permissive, e.g. it will accept many
      grammar and other semantic extensions which might not be legal when
      set to an older standard.

.. option:: --assert

   Enable all assertions.

.. option:: --autoflush

   After every $display or $fdisplay, flush the output stream.  This
   ensures that messages will appear immediately but may reduce
   performance. For best performance call :code:`fflush(stdout)`
   occasionally in the C++ main loop.  Defaults to off, which will buffer
   output as provided by the normal C/C++ standard library IO.

.. option:: --bbox-sys

   Black box any unknown $system task or function calls.  System tasks will
   become no-operations, and system functions will be replaced with unsized
   zero.  Arguments to such functions will be parsed, but not otherwise
   checked.  This prevents errors when linting in the presence of company
   specific PLI calls.

   Using this argument will likely cause incorrect simulation.

.. option:: --bbox-unsup

   Black box some unsupported language features, currently UDP tables, the
   cmos and tran gate primitives, deassign statements, and mixed edge
   errors.  This may enable linting the rest of the design even when
   unsupported constructs are present.

   Using this argument will likely cause incorrect simulation.

.. option:: --bin <filename>

   Rarely needed.  Override the default filename for Verilator itself.
   When a dependency (.d) file is created, this filename will become a
   source dependency, such that a change in this binary will have make
   rebuild the output files.

.. option:: --build

   After generating the SystemC/C++ code, Verilator will invoke the
   toolchain to build the model library (and executable when :vlopt:`--exe`
   is also used). Verilator manages the build itself, and for this --build
   requires GNU Make to be available on the platform.

.. option:: --cc

   Specifies C++ without SystemC output mode; see also :vlopt:`--sc`
   option.

.. option:: --cdc

   Permanently experimental.  Perform some clock domain crossing checks and
   issue related warnings (CDCRSTLOGIC) and then exit; if warnings other
   than CDC warnings are needed make a second run with
   :vlopt:`--lint-only`.  Additional warning information is also written to
   the file :file:`<prefix>__cdc.txt`.

   Currently only checks some items that other CDC tools missed; if you
   have interest in adding more traditional CDC checks, please contact the
   authors.

.. option:: -CFLAGS <flags>

   Add specified C compiler argument to the generated makefiles. For
   multiple flags either pass them as a single argument with space
   separators quoted in the shell (:command:`-CFLAGS "-a -b"`), or use
   multiple -CFLAGS options (:command:`-CFLAGS -a -CFLAGS -b`).

   When make is run on the generated makefile these will be passed to the
   C++ compiler (g++/clang++/msvc++).

.. option:: --clk <signal-name>

   With :vlopt:`--clk`, the specified signal-name is taken as a root clock
   into the model; Verilator will mark the signal as clocker and
   propagate the clocker attribute automatically to other signals downstream in
   that clock tree.

   The provided signal-name is specified using a RTL hierarchy path. For
   example, v.foo.bar.  If the signal is the input to top-module, then
   directly provide the signal name. Alternatively, use a
   :option:`/*verilator&32;clocker*/` metacomment in RTL file to mark the
   signal directly.

   If clock signals are assigned to vectors and then later used as
   individual bits, Verilator will attempt to decompose the vector and
   connect the single-bit clock signals.

   The clocker attribute is useful in cases where Verilator does not
   properly distinguish clock signals from other data signals. Using
   clocker will cause the signal indicated to be considered a clock, and
   remove it from the combinatorial logic reevaluation checking code. This
   may greatly improve performance.

.. option:: --no-clk <signal-name>

   Prevent the specified signal from being marked as clock. See
   :vlopt:`--clk`.

.. option:: --compiler <compiler-name>

   Enables workarounds for the specified C++ compiler (list below).
   Currently this does not change any performance tuning options, but it may
   in the future.

   clang
     Tune for clang.  This may reduce execution speed as it enables several
     workarounds to avoid silly hard-coded limits in clang.  This includes
     breaking deep structures as for msvc as described below.

   gcc
     Tune for GNU C++, although generated code should work on almost any
     compliant C++ compiler.  Currently the default.

   msvc
     Tune for Microsoft Visual C++.  This may reduce execution speed as it
     enables several workarounds to avoid silly hard-coded limits in
     MSVC++.  This includes breaking deeply nested parenthesized
     expressions into sub-expressions to avoid error C1009, and breaking
     deep blocks into functions to avoid error C1061.

.. option:: --converge-limit <loops>

   Rarely needed.  Specifies the maximum number of runtime iterations
   before creating a model failed to converge error.  Defaults to 100.

.. option:: --coverage

   Enables all forms of coverage, alias for :vlopt:`--coverage-line`
   :vlopt:`--coverage-toggle` :vlopt:`--coverage-user`.

.. option:: --coverage-line

   Enables basic block line coverage analysis. See :ref:`Line Coverage`.

.. option:: --coverage-max-width <width>

   Rarely needed.  Specify the maximum bit width of a signal that is
   subject to toggle coverage.  Defaults to 256, as covering large vectors
   may greatly slow coverage simulations.

.. option:: --coverage-toggle

   Enables adding signal toggle coverage.  See :ref:`Toggle Coverage`.

.. option:: --coverage-underscore

   Enable coverage of signals that start with an underscore. Normally,
   these signals are not covered.  See also :vlopt:`--trace-underscore`
   option.

.. option:: --coverage-user

   Enables adding user inserted functional coverage.  See :ref:`User Coverage`.

.. option:: -D<var>=<value>

   Defines the given preprocessor symbol.  Similar to :vlopt:`+define
   <+define+<var>>`, but does not allow multiple definitions with a single
   option using plus signs. "+define" is fairly standard across Verilog
   tools while "-D" is similar to :command:`gcc -D`.

.. option:: --debug

   Run under debug.

   * Select the debug executable of Verilator (if available), this
     generally is a less-optimized binary with symbols present (so GDB can be used on it).
   * Enable debugging messages (equivalent to :vlopt:`--debugi 3 <--debugi>`).
   * Enable internal assertions (equivalent to :vlopt:`--debug-check`).
   * Enable intermediate form dump files (equivalent to :vlopt:`--dump-treei 3
     <--dump-treei>`).
   * Leak to make node numbers unique (equivalent to :vlopt:`--debug-leak
     <--no-debug-leak>`.
   * Call abort() instead of exit() if there are any errors (so GDB can see
     the program state).

.. option:: --debug-check

   Rarely needed.  Enable internal debugging assertion checks, without
   changing debug verbosity.  Enabled automatically with :vlopt:`--debug`
   option.

.. option:: --no-debug-leak

   In :vlopt:`--debug` mode, by default Verilator intentionally leaks
   AstNode instances instead of freeing them, so that each node pointer is
   unique in the resulting tree files and dot files.

   This option disables the leak. This may avoid out-of-memory errors when
   Verilating large models in :vlopt:`--debug` mode.

   Outside of :vlopt:`--debug` mode, AstNode instances should never be
   leaked and this option has no effect.

.. option:: --debugi <level>

   Rarely needed - for developer use.  Set internal debugging level
   globally to the specified debug level (1-10). Higher levels produce more
   detailed messages.

.. option:: --debugi-<srcfile> <level>

   Rarely needed - for developer use.  Set the specified Verilator source
   file to the specified level (e.g. :vlopt:`--debugi-V3Width 9
   <--debugi>`). Higher levels produce more detailed messages.  See
   :vlopt:`--debug` for other implications of enabling debug.

.. option:: --no-decoration

   When creating output Verilated code, minimize comments, white space,
   symbol names and other decorative items, at the cost of greatly reduced
   readability. This may assist C++ compile times. This will not typically
   change the ultimate model's performance, but may in some cases.

.. option:: --default-language <value>

   Select the language to be used by default when first processing each
   Verilog file.  The language value must be "VAMS", "1364-1995",
   "1364-2001", "1364-2001-noconfig", "1364-2005", "1800-2005",
   "1800-2009", "1800-2012", "1800-2017", or "1800+VAMS".

   Any language associated with a particular file extension (see the
   various +<lang>*\ ext+ options) will be used in preference to the
   language specified by :vlopt:`--default-language`.

   The :vlopt:`--default-language` is only recommended for legacy code
   using the same language in all source files, as the preferable option is
   to edit the code to repair new keywords, or add appropriate
   :code:`\`begin_keywords`. For legacy mixed language designs, the various
   ``+<lang>ext+`` options should be used.

   If no language is specified, either by this option or ``+<lang>ext+``
   options, then the latest SystemVerilog language (IEEE 1800-2017) is
   used.

.. option:: +define+<var>=<value>

.. option:: +define+<var>=<value>[+<var2>=<value2>][...]

   Defines the given preprocessor symbol, or multiple symbols if separated
   by plus signs.  Similar to :vlopt:`-D <-D<var>>`; +define is fairly
   standard across Verilog tools while :vlopt:`-D <-D<var>>` is similar to
   :command:`gcc -D`.

.. option:: --dpi-hdr-only

   Only generate the DPI header file.  This option has no effect on the
   name or location of the emitted DPI header file, it is output in
   :vlopt:`--Mdir` as it would be without this option.

.. option:: --dump-defines

   With :vlopt:`-E`, suppress normal output, and instead print a list of
   all defines existing at the end of pre-processing the input
   files. Similar to GCC "-dM" option. This also gives you a way of finding
   out what is predefined in Verilator using the command:

   .. code-block:: bash

       touch foo.v ; verilator -E --dump-defines foo.v

.. option:: --dump-tree

   Rarely needed.  Enable writing .tree debug files with dumping level 3,
   which dumps the standard critical stages.  For details on the format see
   the Verilator Internals manual.  :vlopt:`--dump-tree` is enabled
   automatically with :vlopt:`--debug`, so :vlopt:`--debug --no-dump-tree
   <--dump-tree>` may be useful if the dump files are large and not
   desired.

.. option:: --dump-treei <level>

.. option:: --dump-treei-<srcfile> <level>

   Rarely needed - for developer use.  Set internal tree dumping level
   globally to a specific dumping level or set the specified Verilator
   source file to the specified tree dumping level (e.g.
   :vlopt:`--dump-treei-V3Order 9 <--dump-treei>`).  Level 0 disables dumps
   and is equivalent to :vlopt:`--no-dump-tree <--dump-tree>`.  Level 9
   enables dumping of every stage.

.. option:: --dump-tree-addrids

   Rarely needed - for developer use.  Replace AST node addresses with
   short identifiers in tree dumps to enhance readability.  Each unique
   pointer value is mapped to a unique identifier, but note that this is
   not necessarily unique per node instance as an address might get reused
   by a newly allocated node after a node with the same address has been
   dumped then freed.

.. option:: -E

   Preprocess the source code, but do not compile, similar to C++
   preprocessing using :command:`gcc -E`.  Output is written to standard
   out.  Beware of enabling debugging messages, as they will also go to
   standard out.

   See also :vlopt:`--dump-defines`, :vlopt:`-P`, and
   :vlopt:`--pp-comments` options.

.. option:: --error-limit <value>

   After this number of errors are encountered during Verilator run, exit.
   Warnings are not counted in this limit.  Defaults to 50.

   Does not affect simulation runtime errors, for those see
   :vlopt:`+verilator+error+limit+\<value\>`.

.. option:: --exe

   Generate an executable.  You will also need to pass additional .cpp
   files on the command line that implement the main loop for your
   simulation.

.. option:: --expand-limit <value>

   Rarely needed.  Fine-tune optimizations to set the maximum size of an
   expression in 32-bit words to expand into separate word-based
   statements.

.. option:: -F <file>

   Read the specified file, and act as if all text inside it was specified
   as command line arguments.  Any relative paths are relative to the
   directory containing the specified file.  See also :vlopt:`-f`
   option. Note :option:`-F` is fairly standard across Verilog tools.

.. option:: -f <file>

   Read the specified file, and act as if all text inside it was specified
   as command line arguments.  Any relative paths are relative to the
   current directory.  See also :vlopt:`-F` option. Note :option:`-f` is
   fairly standard across Verilog tools.

   The file may contain :code:`//` comments which are ignored to the end of
   the line.  It may also contain :code:`/* .. */` comments which are
   ignored, be cautious that wildcards are not handled in -f files, and
   that :code:`directory/*` is the beginning of a comment, not a wildcard.
   Any :code:`$VAR`, :code:`$(VAR)`, or :code:`${VAR}` will be replaced
   with the specified environment variable.

.. option:: -FI <file>

   Force include of the specified C++ header file.  All generated C++ files
   will insert a #include of the specified file before any other
   includes. The specified file might be used to contain define prototypes
   of custom :code:`VL_VPRINTF` functions, and may need to include
   :file:`verilatedos.h` as this file is included before any other standard
   includes.

.. option:: --flatten

   Force flattening of the design's hierarchy, with all modules, tasks and
   functions inlined. Typically used with :vlopt:`--xml-only`. Note
   flattening large designs may require significant CPU time, memory and
   storage.

.. option:: -fno-acyc-simp

.. option:: -fno-assemble

.. option:: -fno-case

.. option:: -fno-combine

.. option:: -fno-const

.. option:: -fno-const-bit-op-tree

.. option:: -fno-dedup

.. option:: -fno-expand

.. option:: -fno-gate

.. option:: -fno-inline

.. option:: -fno-life

.. option:: -fno-life-post

.. option:: -fno-localize

.. option:: -fno-merge-cond

.. option:: -fno-merge-cond-motion

.. option:: -fno-merge-const-pool

.. option:: -fno-reloop

.. option:: -fno-reorder

.. option:: -fno-split

.. option:: -fno-subst

.. option:: -fno-subst-const

.. option:: -fno-table

   Rarely needed. Disables one of the internal optimization steps. These
   are typically used only when recommended by a maintainer to help debug
   or work around an issue.

.. option:: -future0 <option>

   Rarely needed.  Suppress an unknown Verilator option for an option that
   takes no additional arguments.  This is used to allow scripts written
   with pragmas for a later version of Verilator to run under a older
   version.  e.g. :code:`-future0 option --option` would on older versions
   that do not understand :code:`--option` or :code:`+option` suppress what
   would otherwise be an invalid option error, and on newer versions that
   implement :code:`--option`, :code:`-future0 option --option` would have
   the :code:`-future0 option` ignored and the :code:`--option` would
   function appropriately.

.. option:: -future1 <option>

   Rarely needed.  Suppress an unknown Verilator option for an option that
   takes an additional argument.  This is used to allow scripts written
   with pragmas for a later version of Verilator to run under a older
   version.  e.g. :code:`-future1 option --option arg` would on older
   versions that do not understand :code:`--option arg` or :code:`+option
   arg` suppress what would otherwise be an invalid option error, and on
   newer versions that implement :code:`--option arg`, :code:`-future1
   option --option arg` would have the :code:`-future1 option` ignored and
   the :code:`--option arg` would function appropriately.

.. option:: -G<name>=<value>

   Overwrites the given parameter of the toplevel module. The value is
   limited to basic data literals:

   Verilog integer literals
     The standard Verilog integer literals are supported, so values like
     32'h8, 2'b00, 4 etc. are allowed. Care must be taken that the single
     quote (I') is properly escaped in an interactive shell, e.g.,
     as :code:`-GWIDTH=8'hx`.

   C integer literals
     It is also possible to use C integer notation, including hexadecimal
     (0x..), octal (0..) or binary (0b..) notation.

   Double literals
     Double literals must be one of the following styles:
      - contains a dot (.) (e.g. 1.23)
      - contains an exponent (e/E) (e.g. 12e3)
      - contains p/P for hexadecimal floating point in C99 (e.g. 0x123.ABCp1)

   Strings
     Strings must be in double quotes (""). They must be escaped properly
     on the command line, e.g. as :code:`-GSTR="\"My String\""` or
     :code:`-GSTR='"My String"'`.

.. option:: --gate-stmts <value>

   Rarely needed.  Set the maximum number of statements that may be present
   in an equation for the gate substitution optimization to inline that
   equation.

.. option:: --gdb

   Run Verilator underneath an interactive GDB (or VERILATOR_GDB
   environment variable value) session.  See also :vlopt:`--gdbbt` option.

.. option:: --gdbbt

   If :vlopt:`--debug` is specified, run Verilator underneath a GDB process
   and print a backtrace on exit, then exit GDB immediately.  Without
   :vlopt:`--debug` or if GDB doesn't seem to work, this flag is ignored.
   Intended for easy creation of backtraces by users; otherwise see the
   :vlopt:`--gdb` option.

.. option:: --generate-key

   Generate a true-random key suitable for use with :vlopt:`--protect-key`,
   print it, and exit immediately.

.. option:: --getenv <variable>

   If the variable is declared in the environment, print it and exit
   immediately. Otherwise, if it's built into Verilator
   (e.g. VERILATOR_ROOT), print that and exit immediately. Otherwise, print
   a newline and exit immediately. This can be useful in makefiles. See
   also :vlopt:`-V`, and the various :file:`*.mk` files.

.. option:: --help

   Displays this message and program version and exits.

.. option:: --hierarchical

   Enable hierarchical Verilation otherwise
   :option:`/*verilator&32;hier_block*/` metacomment is ignored.  See
   :ref:`Hierarchical Verilation`.

.. option:: -I<dir>

   See :vlopt:`-y`.

.. option:: --if-depth <value>

   Rarely needed.  Set the depth at which the IFDEPTH warning will fire,
   defaults to 0 which disables this warning.

.. option:: +incdir+<dir>

   See :vlopt:`-y`.

.. option:: --inline-mult <value>

   Tune the inlining of modules.  The default value of 2000 specifies that up
   to 2000 new operations may be added to the model by inlining, if more than
   this number of operations would result, the module is not inlined.  Larger
   values, or a value < 1 will inline everything, will lead to longer compile
   times, but potentially faster simulation speed.  This setting is ignored
   for very small modules; they will always be inlined, if allowed.

.. option:: --instr-count-dpi <value>

   Assumed dynamic instruction count of the average DPI import. This is used
   by the partitioning algorithm when creating a multithread model. The
   default value is 200. Adjusting this to an appropriate value can yield
   performance improvements in multithreaded models. Ignored when creating a
   single threaded model.

.. option:: -j [<value>]

   Specify the level of parallelism for :vlopt:`--build`. The <value> must
   be a positive integer specifying the maximum number of parallel build
   jobs, or can be omitted. When <value> is omitted, the build will not try
   to limit the number of parallel build jobs but attempt to execute all
   independent build steps in parallel.

.. option:: --l2-name <value>

   Instead of using the module name when showing Verilog scope, use the
   name provided. This allows simplifying some Verilator-embedded modeling
   methodologies. Default is an l2-name matching the top module. The
   default before Verilator 3.884 was ``--l2-name v``.

   For example, the program :code:`module t; initial $display("%m");
   endmodule` will show by default "t". With ``--l2-name v`` it will print
   "v".

.. option:: --language <value>

   A synonym for :vlopt:`--default-language`, for compatibility with other
   tools and earlier versions of Verilator.

.. option:: -LDFLAGS <flags>

   Add specified C linker arguments to the generated makefiles.  For multiple
   flags either pass them as a single argument with space separators quoted
   in the shell (``-LDFLAGS "-a -b"``), or use multiple -LDFLAGS arguments
   (``-LDFLAGS -a -LDFLAGS -b``).

   When make is run on the generated makefile these will be passed to the
   C++ linker (ld) **after** the primary file being linked.  This flag is
   called :vlopt:`-LDFLAGS` as that's the traditional name in simulators;
   it's would have been better called LDLIBS as that's the Makefile
   variable it controls.  (In Make, LDFLAGS is before the first object,
   LDLIBS after.  -L libraries need to be in the Make variable LDLIBS, not
   LDFLAGS.)

.. option:: --lib-create <name>

   Produces C++, Verilog wrappers and a Makefile which can in turn produce
   a DPI library which can be used by Verilator or other simulators along
   with the corresponding Verilog wrapper.  The Makefile will build both a
   static and dynamic version of the library named :file:`lib<name>.a` and
   :file:`lib<name>.so` respectively.  This is done because some simulators
   require a dynamic library, but the static library is arguably easier to
   use if possible.  :vlopt:`--protect-lib` implies :vlopt:`--protect-ids`.

   When using :vlopt:`--lib-create` it is advised to also use
   :vlopt:`--timescale-override /1fs <--timescale-override>` to ensure the
   model has a time resolution that is always compatible with the time
   precision of the upper instantiating module.

   See also :vlopt:`--protect-lib`.

.. option:: +libext+<ext>[+<ext>][...]

   Specify the extensions that should be used for finding modules.  If for
   example module "my" is referenced, look in :file:`my.<ext>`.  Note
   "+libext+" is fairly standard across Verilog tools.  Defaults to
   ".v+.sv".

.. option:: --lint-only

   Check the files for lint violations only, do not create any other
   output.

   You may also want the :vlopt:`-Wall` option to enable messages that are
   considered stylistic and not enabled by default.

   If the design is not to be completely Verilated see also the
   :vlopt:`--bbox-sys` and :vlopt:`--bbox-unsup` options.

.. option:: --make <build-tool>

   Generates a script for the specified build tool.

   Supported values are ``gmake`` for GNU Make and ``cmake`` for CMake.
   Both can be specified together.  If no build tool is specified, gmake is
   assumed.  The executable of gmake can be configured via environment
   variable "MAKE".

   When using :vlopt:`--build` Verilator takes over the responsibility of
   building the model library/executable.  For this reason :option:`--make`
   cannot be specified when using :vlopt:`--build`.

.. option:: -MAKEFLAGS <string>

   When using :vlopt:`--build`, add the specified argument to the invoked
   make command line.  For multiple flags either pass them as a single
   argument with space separators quoted in the shell (e.g.  ``-MAKEFLAGS
   "-a -b"``), or use multiple -MAKEFLAGS arguments
   (e.g. ``-MAKEFLAGS -l -MAKEFLAGS -k``). Use of this option should not be
   required for simple builds using the host toolchain.

.. option:: --max-num-width <value>

   Set the maximum number literal width (e.g. in 1024'd22 this it the
   1024).  Defaults to 64K.

.. option:: --Mdir <directory>

   Specifies the name of the Make object directory.  All generated files
   will be placed in this directory.  If not specified, "obj_dir" is used.
   The directory is created if it does not exist and the parent directories
   exist; otherwise manually create the Mdir before calling Verilator.

.. option:: --MMD

.. option:: --no-MMD

   Enable/disable creation of .d dependency files, used for make dependency
   detection, similar to gcc -MMD option.  By default this option is
   enabled for :vlopt:`--cc` or :vlopt:`--sc` modes.

.. option:: --mod-prefix <topname>

   Specifies the name to prepend to all lower level classes.  Defaults to
   the same as :vlopt:`--prefix`.

.. option:: --MP

   When creating .d dependency files with :vlopt:`--MMD` option, make phony
   targets.  Similar to :command:`gcc -MP` option.

.. option:: +notimingchecks

   Ignored for compatibility with other simulators.

.. option:: -O0

   Disables optimization of the model.

.. option:: -O3

   Enables slow optimizations for the code Verilator itself generates (as
   opposed to :vlopt:`-CFLAGS -O3 <-CFLAGS>` which effects the C compiler's
   optimization.  :vlopt:`-O3` may improve simulation performance at the
   cost of compile time.  This currently sets :vlopt:`--inline-mult -1
   <--inline-mult>`.

.. option:: -O<optimization-letter>

   Rarely needed.  Enables or disables a specific optimizations, with the
   optimization selected based on the letter passed.  A lowercase letter
   disables an optimization, an upper case letter enables it.  This option
   is deprecated and the various `-f<optimization>` arguments should be
   used instead.

.. option:: -o <executable>

   Specify the name for the final executable built if using :vlopt:`--exe`.
   Defaults to the :vlopt:`--prefix` if not specified.

.. option:: --no-order-clock-delay

   Rarely needed.  Disables a bug fix for ordering of clock enables with
   delayed assignments.  This option should only be used when suggested by
   the developers.

.. option:: --output-split <statements>

   Enables splitting the output .cpp files into multiple outputs.  When a
   C++ file exceeds the specified number of operations, a new file will be
   created at the next function boundary.  In addition, if the total output
   code size exceeds the specified value, VM_PARALLEL_BUILDS will be set to
   1 by default in the generated make files, making parallel compilation
   possible. Using :vlopt:`--output-split` should have only a trivial
   impact on model performance. But can greatly improve C++ compilation
   speed. The use of "ccache" (set for you if present at configure time) is
   also more effective with this option.

   This option is on by default with a value of 20000. To disable, pass with a
   value of 0.

.. option:: --output-split-cfuncs <statements>

   Enables splitting functions in the output .cpp files into multiple
   functions.  When a generated function exceeds the specified number of
   operations, a new function will be created.  With
   :vlopt:`--output-split`, this will enable the C++ compiler to compile
   faster, at a small loss in performance that gets worse with decreasing
   split values.  Note that this option is stronger than
   :vlopt:`--output-split` in the sense that :vlopt:`--output-split` will
   not split inside a function.

   Defaults to the value of :vlopt:`--output-split`, unless explicitly
   specified.

.. option:: --output-split-ctrace <statements>

   Similar to :vlopt:`--output-split-cfuncs`, enables splitting trace
   functions in the output .cpp files into multiple functions.

   Defaults to the value of :vlopt:`--output-split`, unless explicitly
   specified.

.. option:: -P

   With :vlopt:`-E`, disable generation of :code:`&96;line` markers and
   blank lines, similar to :command:`gcc -P`.

.. option:: --pins-bv <width>

   Specifies SystemC inputs/outputs of greater than or equal to <width>
   bits wide should use sc_bv's instead of uint32/uint64_t's.  The
   default is "--pins-bv 65", and the value must be less than or equal
   to 65.  Versions before Verilator 3.671 defaulted to "--pins-bv 33".
   The more sc_bv is used, the worse for performance.  Use the
   :option:`/*verilator&32;sc_bv*/` metacomment to select specific ports to
   be sc_bv.

.. option:: --pins-sc-uint

   Specifies SystemC inputs/outputs of greater than 2 bits wide should use
   sc_uint between 2 and 64.  When combined with the
   :vlopt:`--pins-sc-biguint` combination, it results in sc_uint being used
   between 2 and 64 and sc_biguint being used between 65 and 512.

.. option:: --pins-sc-biguint

   Specifies SystemC inputs/outputs of greater than 65 bits wide should use
   sc_biguint between 65 and 512, and sc_bv from 513 upwards.  When
   combined with the :vlopt:`--pins-sc-uint` combination, it results in
   sc_uint being used between 2 and 64 and sc_biguint being used between 65
   and 512.

.. option:: --pins-uint8

   Specifies SystemC inputs/outputs that are smaller than the
   :vlopt:`--pins-bv` setting and 8 bits or less should use uint8_t instead
   of uint32_t.  Likewise pins of width 9-16 will use uint16_t instead of
   uint32_t.

.. option:: --pins64

   Backward compatible alias for :vlopt:`--pins-bv 65 <--pins-bv>`.  Note
   that's a 65, not a 64.

.. option:: --no-pins64

   Backward compatible alias for :vlopt:`--pins-bv 33 <--pins-bv>`.

.. option:: --pipe-filter <command>

   Rarely needed.  Verilator will spawn the specified command as a
   subprocess pipe, to allow the command to perform custom edits on the
   Verilog code before it reaches Verilator.

   Before reading each Verilog file, Verilator will pass the file name to
   the subprocess' stdin with :code:`read "<filename>"`.  The filter may
   then read the file and perform any filtering it desires, and feeds the
   new file contents back to Verilator on stdout by first emitting a line
   defining the length in bytes of the filtered output
   :code:`Content-Length: <bytes>`, followed by the new filtered
   contents. Output to stderr from the filter feeds through to Verilator's
   stdout and if the filter exits with non-zero status Verilator
   terminates.  See the file:`t/t_pipe_filter` test for an example.

   To debug the output of the filter, try using the :vlopt:`-E` option to
   see preprocessed output.

.. option:: --pp-comments

   With :vlopt:`-E`, show comments in preprocessor output.

.. option:: --prefix <topname>

   Specifies the name of the top level class and makefile.  Defaults to V
   prepended to the name of the :vlopt:`--top` option, or V prepended to
   the first Verilog filename passed on the command line.

.. option:: --private

   Opposite of :vlopt:`--public`.  Is the default; this option exists for
   backwards compatibility.

.. option:: --prof-c

   When compiling the C++ code, enable the compiler's profiling flag
   (e.g. :code:`g++ -pg`). See :ref:`Profiling`.

   Using :vlopt:`--prof-cfuncs` also enables :vlopt:`--prof-c`.

.. option:: --prof-cfuncs

   Modify the created C++ functions to support profiling.  The functions
   will be minimized to contain one "basic" statement, generally a single
   always block or wire statement.  (Note this will slow down the
   executable by ~5%.)  Furthermore, the function name will be suffixed
   with the basename of the Verilog module and line number the statement
   came from.  This allows gprof or oprofile reports to be correlated with
   the original Verilog source statements. See :ref:`Profiling`.

   Using :vlopt:`--prof-cfuncs` also enables :vlopt:`--prof-c`.

.. option:: --prof-exec

   Enable collection of execution trace, that can be converted into a gantt
   chart with verilator_gantt See :ref:`Execution Profiling`.

.. option:: --prof-pgo

   Enable collection of profiling data for profile guided Verilation. Currently
   this is only useful with :vlopt:`--threads`. See :ref:`Thread PGO`.

.. option:: --prof-threads

   Deprecated. Same as --prof-exec and --prof-pgo together.

.. option:: --protect-ids

   Hash any private identifiers (variable, module, and assertion block
   names that are not on the top level) into hashed random-looking
   identifiers, resulting after compilation in protected library binaries
   that expose less design information.  This hashing uses the provided or
   default :vlopt:`--protect-key`, see important details there.

   Verilator will also create a :file:`<prefix>__idmap.xml` file which
   contains the mapping from the hashed identifiers back to the original
   identifiers. This idmap file is to be kept private, and is to assist
   mapping any simulation runtime design assertions, coverage, or trace
   information, which will report the hashed identifiers, back to the
   original design's identifier names.

   Using DPI imports/exports is allowed and generally relatively safe in
   terms of information disclosed, which is limited to the DPI function
   prototypes.  Use of the VPI is not recommended as many design details
   may be exposed, and an INSECURE warning will be issued.

.. option:: --protect-key <key>

   Specifies the private key for :vlopt:`--protect-ids`. For best security
   this key should be 16 or more random bytes, a reasonable secure choice
   is the output of :command:`verilator --generate-key` . Typically, a key
   would be created by the user once for a given protected design library,
   then every Verilator run for subsequent versions of that library would
   be passed the same :vlopt:`--protect-key`. Thus, if the input Verilog is
   similar between library versions (Verilator runs), the Verilated code
   will likewise be mostly similar.

   If :vlopt:`--protect-key` is not specified and a key is needed,
   Verilator will generate a new key for every Verilator run. As the key is
   not saved, this is best for security, but means every Verilator run will
   give vastly different output even for identical input, perhaps harming
   compile times (and certainly thrashing any "ccache").

.. option:: --protect-lib <name>

   Produces a DPI library similar to :vlopt:`--lib-create`, but hides
   internal design details.  :vlopt:`--protect-lib` implies
   :vlopt:`--protect-ids`, and :vlopt:`--lib-create`.

   This allows for the secure delivery of sensitive IP without the need for
   encrypted RTL (i.e. IEEE P1735).  See :file:`examples/make_protect_lib`
   in the distribution for a demonstration of how to build and use the DPI
   library.

.. option:: --public

   This is only for historical debug use.  Using it may result in
   mis-simulation of generated clocks.

   Declares all signals and modules public.  This will turn off signal
   optimizations as if all signals had a :option:`/*verilator&32;public*/`
   metacomments and inlining.  This will also turn off inlining as if all
   modules had a :option:`/*verilator&32;public_module*/`, unless the
   module specifically enabled it with
   :option:`/*verilator&32;inline_module*/`.

.. option:: --public-flat-rw

   Declares all variables, ports and wires public as if they had
   :code:`/*verilator public_flat_rw @
   (<variable's_source_process_edge>)*/` metacomments.  This will make them
   VPI accessible by their flat name, but not turn off module inlining.
   This is particularly useful in combination with :vlopt:`--vpi`. This may
   also in some rare cases result in mis-simulation of generated clocks.
   Instead of this global option, marking only those signals that need
   public_flat_rw is typically significantly better performing.

.. option:: -pvalue+<name>=<value>

   Overwrites the given parameter(s) of the toplevel module. See :vlopt:`-G
   <-G<name>>` for a detailed description.

.. option:: --quiet-exit

   When exiting due to an error, do not display the "Exiting due to Errors"
   nor "Command Failed" messages.

.. option:: --relative-includes

   When a file references an include file, resolve the filename relative to
   the path of the referencing file, instead of relative to the current
   directory.

.. option:: --reloop-limit

   Rarely needed. Verilator attempts to turn some common sequences of
   statements into loops in the output. This argument specifies the minimum
   number of iterations the resulting loop needs to have in order to perform
   this transformation. Default limit is 40. A smaller number may slightly
   improve C++ compilation time on designs where these sequences are common,
   however effect on model performance requires benchmarking.

.. option:: --report-unoptflat

   Extra diagnostics for UNOPTFLAT warnings. This includes for each loop,
   the 10 widest variables in the loop, and the 10 most fanned out
   variables in the loop. These are candidates for splitting into multiple
   variables to break the loop.

   In addition produces a GraphViz DOT file of the entire strongly
   connected components within the source associated with each loop. This
   is produced irrespective of whether :vlopt:`--dump-tree` is set. Such
   graphs may help in analyzing the problem, but can be very large indeed.

   Various commands exist for viewing and manipulating DOT files. For
   example the "dot" command can be used to convert a DOT file to a PDF for
   printing. For example:

   .. code-block:: bash

        dot -Tpdf -O Vt_unoptflat_simple_2_35_unoptflat.dot

   will generate a PDF :file:`Vt_unoptflat_simple_2_35_unoptflat.dot.pdf`
   from the DOT file.

   As an alternative, the :command:`xdot` command can be used to view DOT
   files interactively:

   .. code-block:: bash

        xdot Vt_unoptflat_simple_2_35_unoptflat.dot

.. option:: --rr

   Run Verilator and record with the :command:`rr` command.  See:
   rr-project.org.

.. option:: --savable

   Enable including save and restore functions in the generated model.  See
   :ref:`Save/Restore`.

.. option:: --sc

   Specifies SystemC output mode; see also :vlopt:`--cc` option.

.. option:: --skip-identical

.. option:: --no-skip-identical

   Rarely needed.  Disables or enables skipping execution of Verilator if
   all source files are identical, and all output files exist with newer
   dates.  By default this option is enabled for :vlopt:`--cc` or
   :vlopt:`--sc` modes only.

.. option:: --stats

   Creates a dump file with statistics on the design in
   :file:`<prefix>__stats.txt`.

.. option:: --stats-vars

   Creates more detailed statistics, including a list of all the variables
   by size (plain :vlopt:`--stats` just gives a count).  See
   :vlopt:`--stats`, which is implied by this.

.. option:: --structs-packed

   Converts all unpacked structures to packed structures and issues a
   UNPACKED warning.  Currently this is the default and
   :vlopt:`--no-structs-packed <--structs-packed>` will not work.
   Specifying this option allows for forward compatibility when a future
   version of Verilator no longer always packs unpacked structures.

.. option:: -sv

   Specifies SystemVerilog language features should be enabled; equivalent
   to :vlopt:`--language 1800-2017 <--language>`.  This option is selected
   by default, it exists for compatibility with other simulators.

.. option:: +systemverilogext+<ext>

   A synonym for :vlopt:`+1800-2017ext+\<ext\>`.

.. option:: --threads <threads>

.. option:: --no-threads

   With "--threads 0" or "--no-threads", the default, the generated model
   is not thread safe. With "--threads 1", the generated model is single
   threaded but may run in a multithreaded environment. With "--threads N",
   where N >= 2, the model is generated to run multithreaded on up to N
   threads. See :ref:`Multithreading`. This option also applies to
   :vlopt:`--trace` (but not :vlopt:`--trace-fst`).

.. option:: --threads-dpi all

.. option:: --threads-dpi none

.. option:: --threads-dpi pure

   When using :vlopt:`--threads`, controls which DPI imported tasks and
   functions are considered thread safe.

   With "--threads-dpi all",
     Enable Verilator to assume all DPI imports are threadsafe, and to use
     thread-local storage for communication with DPI, potentially improving
     performance. Any DPI libraries need appropriate mutexes to avoid
     undefined behavior.

   With "--threads-dpi none",
     Verilator assume DPI imports are not thread safe, and Verilator will
     serialize calls to DPI imports by default, potentially harming
     performance.

   With "--threads-dpi pure", the default,
     Verilator assumes DPI pure imports are threadsafe, but non-pure DPI
     imports are not.

   See also :vlopt:`--instr-count-dpi` option.

.. option:: --threads-max-mtasks <value>

   Rarely needed.  When using :vlopt:`--threads`, specify the number of
   mtasks the model is to be partitioned into. If unspecified, Verilator
   approximates a good value.

.. option:: --timescale <timeunit>/<timeprecision>

   Sets default timescale, timeunit and timeprecision for when "`timescale"
   does not occur before a given module.  Default is "1ps/1ps" (to match
   SystemC).  This is overridden by :vlopt:`--timescale-override`.

.. option:: --timescale-override <timeunit>/<timeprecision>

.. option:: --timescale-override /<timeprecision>

   Overrides all "\`timescale"s in sources. The timeunit may be left empty
   to specify only to override the timeprecision, e.g. "/1fs".

   The time precision must be consistent with SystemC's
   "sc_set_time_resolution()", or the C++ code instantiating the Verilated
   module.  As "1fs" is the finest time precision it may be desirable to
   always use a precision of "1fs".

.. option:: --top <topname>

.. option:: --top-module <topname>

   When the input Verilog contains more than one top level module,
   specifies the name of the Verilog module to become the top level module,
   and sets the default for :vlopt:`--prefix` if not explicitly specified.
   This is not needed with standard designs with only one top.  See also
   :option:`MULTITOP` warning.

.. option:: --trace

   Adds waveform tracing code to the model using VCD format. This overrides
   :vlopt:`--trace-fst`.

   Verilator will generate additional :file:`<prefix>__Trace*.cpp` files
   that will need to be compiled.  In addition :file:`verilated_vcd_sc.cpp`
   (for SystemC traces) or :file:`verilated_vcd_c.cpp` (for both) must be
   compiled and linked in.  If using the Verilator generated Makefiles,
   these files will be added to the source file lists for you.  If you are
   not using the Verilator Makefiles, you will need to add these to your
   Makefile manually.

   Having tracing compiled in may result in some small performance losses,
   even when tracing is not turned on during model execution.

   When using :vlopt:`--threads`, VCD tracing is parallelized, using the
   same number of threads as passed to :vlopt:`--threads`.

.. option:: --trace-coverage

   With :vlopt:`--trace` and ``--coverage-*``, enable tracing to include a
   traced signal for every :vlopt:`--coverage-line` or
   :vlopt:`--coverage-user`\ -inserted coverage point, to assist in
   debugging coverage items.  Note :vlopt:`--coverage-toggle` does not get
   additional signals added, as the original signals being toggle-analyzed
   are already visible.

   The added signal will be a 32-bit value which will increment on each
   coverage occurrence. Due to this, this option may greatly increase trace
   file sizes and reduce simulation speed.

.. option:: --trace-depth <levels>

   Specify the number of levels deep to enable tracing, for example
   :vlopt:`--trace-depth 1 <--trace-depth>` to only see the top level's
   signals.  Defaults to the entire model.  Using a small number will
   decrease visibility, but greatly improve simulation performance and
   trace file size.

.. option:: --trace-fst

   Enable FST waveform tracing in the model. This overrides
   :vlopt:`--trace`.  See also :vlopt:`--trace-threads` option.

.. option:: --trace-max-array *depth*

   Rarely needed.  Specify the maximum array depth of a signal that may be
   traced.  Defaults to 32, as tracing large arrays may greatly slow traced
   simulations.

.. option:: --trace-max-width *width*

   Rarely needed.  Specify the maximum bit width of a signal that may be
   traced.  Defaults to 256, as tracing large vectors may greatly slow
   traced simulations.

.. option:: --no-trace-params

   Disable tracing of parameters.

.. option:: --trace-structs

   Enable tracing to show the name of packed structure, union, and packed
   array fields, rather than a single combined packed bus.  Due to VCD file
   format constraints this may result in significantly slower trace times
   and larger trace files.

.. option:: --trace-threads *threads*

   Enable waveform tracing using separate threads. This is typically faster
   in simulation runtime but uses more total compute. This option only
   applies to :vlopt:`--trace-fst`. FST tracing can utilize at most
   "--trace-threads 2". This overrides :vlopt:`--no-threads`.

   This option is accepted, but has absolutely no effect with
   :vlopt:`--trace`, which respects :vlopt:`--threads` instead.

.. option:: --trace-underscore

   Enable tracing of signals or modules that start with an
   underscore. Normally, these signals are not output during tracing.  See
   also :vlopt:`--coverage-underscore` option.

.. option:: -U<var>

   Undefines the given preprocessor symbol.

.. option:: --unroll-count <loops>

   Rarely needed.  Specifies the maximum number of loop iterations that may be
   unrolled.  See also :option:`BLKLOOPINIT` warning.

.. option:: --unroll-stmts *statements*

   Rarely needed.  Specifies the maximum number of statements in a loop for
   that loop to be unrolled. See also :option:`BLKLOOPINIT` warning.

.. option:: --unused-regexp *regexp*

   Rarely needed.  Specifies a simple regexp with \* and ? that if a signal
   name matches will suppress the UNUSED warning.  Defaults to
   "\*unused\*".  Setting it to "" disables matching.

.. option:: -V

   Shows the verbose version, including configuration information compiled
   into Verilator.  (Similar to :command:`perl -V`.)  See also
   :vlopt:`--getenv` option.

.. option:: -v *filename*

   Read the filename as a Verilog library.  Any modules in the file may be
   used to resolve instances in the top level module, else ignored.  Note
   "-v" is fairly standard across Verilog tools.

.. option:: --no-verilate

   When using :vlopt:`--build`, disable generation of C++/SystemC code, and
   execute only the build. This can be useful for rebuilding Verilated code
   produced by a previous invocation of Verilator.

.. option:: +verilog1995ext+<ext>

   Synonym for :vlopt:`+1364-1995ext+\<ext\>`.

.. option:: +verilog2001ext+<ext>

   Synonym for :vlopt:`+1364-2001ext+\<ext\>`.

.. option:: --version

   Displays program version and exits.

.. option:: --vpi

   Enable use of VPI and linking against the :file:`verilated_vpi.cpp` files.

.. option:: --waiver-output *filename*

   Generate a waiver file which contains all waiver statements to suppress
   the warnings emitted during this Verilator run. This in particular is
   useful as a starting point for solving linter warnings or suppressing
   them systematically.

   The generated file is in the Verilator Configuration format, see
   :ref:`Configuration Files`, and can directly be consumed by
   Verilator. The standard file extension is ".vlt".

.. option:: -Wall

   Enable all code style warnings, including code style warnings that are
   normally disabled by default. Equivalent to :vlopt:`-Wwarn-lint`
   :vlopt:`-Wwarn-style`.  Excludes some specialty warnings,
   i.e. IMPERFECTSCH.

.. option:: -Werror-<message>

   Promote the specified warning message into an error message.  This is
   generally to discourage users from violating important site-wide rules,
   for example "-Werror-NOUNOPTFLAT".

.. option:: -Wfuture-<message>

   Rarely needed.  Suppress unknown Verilator comments or warning messages
   with the given message code.  This is used to allow code written with
   pragmas for a later version of Verilator to run under a older version;
   add "-Wfuture-" arguments for each message code or comment that the new
   version supports which the older version does not support.

.. option:: -Wno-<message>

   Disable the specified warning/error message.  This will override any
   lint_on directives in the source, i.e. the warning will still not be
   printed.

.. option:: -Wno-context

   Disable showing the suspected context of the warning message by quoting
   the source text at the suspected location.  This can be used to appease
   tools which process the warning messages but may get confused by lines
   from the original source.

.. option:: -Wno-fatal

   When warnings are detected, print them, but do not terminate Verilator.

   Having warning messages in builds can be sloppy.  It is recommended you
   cleanup your code, use inline lint_off, or use ``-Wno-...`` options
   rather than using this option.

.. option:: -Wno-lint

   Disable all lint related warning messages, and all style warnings.  This is
   equivalent to ``-Wno-ALWCOMBORDER -Wno-BSSPACE -Wno-CASEINCOMPLETE
   -Wno-CASEOVERLAP -Wno-CASEX -Wno-CASTCONST -Wno-CASEWITHX -Wno-CMPCONST -Wno-COLONPLUS
   -Wno-ENDLABEL -Wno-IMPLICIT -Wno-LITENDIAN -Wno-PINCONNECTEMPTY
   -Wno-PINMISSING -Wno-SYNCASYNCNET -Wno-UNDRIVEN -Wno-UNSIGNED -Wno-UNUSED
   -Wno-WIDTH`` plus the list shown for Wno-style.

   It is strongly recommended you cleanup your code rather than using this
   option, it is only intended to be use when running test-cases of code
   received from third parties.

.. option:: -Wno-style

   Disable all code style related warning messages (note by default they are
   already disabled).  This is equivalent to ``-Wno-DECLFILENAME -Wno-DEFPARAM
   -Wno-EOFNEWLINE -Wno-IMPORTSTAR -Wno-INCABSPATH -Wno-PINCONNECTEMPTY
   -Wno-PINNOCONNECT -Wno-SYNCASYNCNET -Wno-UNDRIVEN -Wno-UNUSED
   -Wno-VARHIDDEN``.

.. option:: -Wpedantic

   Warn on any construct demanded by IEEE, and disable all Verilator
   extensions that may interfere with IEEE compliance to the standard
   defined with :vlopt:`--default-language` (etc).  Similar to
   :command:`gcc -Wpedantic`.  Rarely used, and intended only for strict
   compliance tests.

.. option:: -Wwarn-<message>

   Enables the specified warning message.

.. option:: -Wwarn-lint

   Enable all lint related warning messages (note by default they are already
   enabled), but do not affect style messages.  This is equivalent to
   ``-Wwarn-ALWCOMBORDER -Wwarn-BSSPACE -Wwarn-CASEINCOMPLETE
   -Wwarn-CASEOVERLAP -Wwarn-CASEX -Wwarn-CASTCONST -Wwarn-CASEWITHX -Wwarn-CMPCONST
   -Wwarn-COLONPLUS -Wwarn-ENDLABEL -Wwarn-IMPLICIT -Wwarn-LITENDIAN
   -Wwarn-PINMISSING -Wwarn-REALCVT -Wwarn-UNSIGNED -Wwarn-WIDTH``.

.. option:: -Wwarn-style

   Enable all code style related warning messages.  This is equivalent to
   ``-Wwarn ASSIGNDLY -Wwarn-DECLFILENAME -Wwarn-DEFPARAM -Wwarn-EOFNEWLINE
   -Wwarn-INCABSPATH -Wwarn-PINNOCONNECT -Wwarn-SYNCASYNCNET -Wwarn-UNDRIVEN
   -Wwarn-UNUSED -Wwarn-VARHIDDEN``.

.. option:: --x-assign 0

.. option:: --x-assign 1

.. option:: --x-assign fast (default)

.. option:: --x-assign unique

   Controls the two-state value that is substituted when an explicit X
   value is encountered in the source.  "--x-assign fast", the default,
   converts all Xs to whatever is best for performance.  "--x-assign 0"
   converts all Xs to 0s, and is also fast.  "--x-assign 1" converts all Xs
   to 1s, this is nearly as fast as 0, but more likely to find reset bugs
   as active high logic will fire. Using "--x-assign unique" will result in
   all explicit Xs being replaced by a constant value determined at
   runtime. The value is determined by calling a function at initialization
   time. This enables randomization of Xs with different seeds on different
   executions. This method is the slowest, but safest for finding reset
   bugs.

   If using "--x-assign unique", you may want to seed your random number
   generator such that each regression run gets a different randomization
   sequence. The simplest is to use the :vlopt:`+verilator+seed+\<value\>`
   runtime option.  Alternatively use the system's :code:`srand48()` or for
   Windows :code:`srand()` function to do this.  You'll probably also want
   to print any seeds selected, and code to enable rerunning with that same
   seed so you can reproduce bugs.

   .. note::

      This option applies only to values which are explicitly written as X
      in modules (not classes) in the Verilog source code. Initial values
      of clocks are set to 0 unless `--x-initial-edge` is
      specified. Initial values of all other state holding variables are
      controlled with `--x-initial`.

.. option:: --x-initial 0

.. option:: --x-initial fast

.. option:: --x-initial unique (default)

   Controls the two-state value that is used to initialize variables that
   are not otherwise initialized.

   "--x-initial 0",
     initializes all otherwise uninitialized variables to zero.

   "--x-initial unique", the default,
     initializes variables using a function, which determines the value to
     use each initialization. This gives greatest flexibility and allows
     finding reset bugs.  See :ref:`Unknown states`.

   "--x-initial fast",
     is best for performance, and initializes all variables to a state
     Verilator determines is optimal.  This may allow further code
     optimizations, but will likely hide any code bugs relating to missing
     resets.

   .. note::

      This option applies only to initial values of variables. Initial
      values of clocks are set to 0 unless :vlopt:`--x-initial-edge` is
      specified.

.. option:: --x-initial-edge

   Enables emulation of event driven simulators which generally trigger an
   edge on a transition from X to 1 (posedge) or X to 0 (negedge). Thus the
   following code, where :code:`rst_n` is uninitialized would set
   :code:`res_n` to :code:`1'b1` when :code:`rst_n` is first set to zero:

   .. code-block:: sv

        reg  res_n = 1'b0;

        always @(negedge rst_n) begin
           if (rst_n == 1'b0) begin
              res_n <= 1'b1;
           end
        end

   In Verilator, by default, uninitialized clocks are given a value of
   zero, so the above :code:`always` block would not trigger.

   While it is not good practice, there are some designs that rely on X
   rarr 0 triggering a negedge, particularly in reset sequences. Using
   :vlopt:`--x-initial-edge` with Verilator will replicate this
   behavior. It will also ensure that X rarr 1 triggers a posedge.

   .. note::

      Using this option can affect convergence, andit may be necessary to
      use :vlopt:`--converge-limit` to increase the number of convergence
      iterations. This may be another indication of problems with the
      modeled design that should be addressed.

.. option:: --xml-only

   Create XML output only, do not create any other output.

   The XML format is intended to be used to leverage Verilator's parser and
   elaboration to feed to other downstream tools. Be aware that the XML
   format is still evolving; there will be some changes in future versions.

.. option:: --xml-output <filename>

   Filename for XML output file. Using this option automatically sets
   :vlopt:`--xml-only`.

.. option:: -y <dir>

   Add the directory to the list of directories that should be searched for
   include files or libraries.  The three flags :vlopt:`-y`,
   :vlopt:`+incdir+\<dir\>` and :vlopt:`-I\<dir\>` have similar effect;
   :vlopt:`+incdir+\<dir\>` and :vlopt:`-y` are fairly standard across
   Verilog tools while :vlopt:`-I\<dir\>` is used by many C++ compilers.

   Verilator defaults to the current directory "-y ." and any specified
   :vlopt:`--Mdir`, though these default paths are used after any user
   specified directories.  This allows '-y "$(pwd)"' to be used if absolute
   filenames are desired for error messages instead of relative filenames.


.. _Configuration Files:

Configuration Files
===================

In addition to the command line, warnings and other features for the
:command:`verilator` command may be controlled with configuration files,
typically named with the .vlt extension (what makes it a configuration file
is the :option:`\`verilator_config` directive). An example:

.. code-block:: sv

     `verilator_config
     lint_off -rule WIDTH
     lint_off -rule CASEX  -file "silly_vendor_code.v"

This disables WIDTH warnings globally, and CASEX for a specific file.

Configuration files are fed through the normal Verilog preprocessor prior
to parsing, so "\`ifdef", "\`define", and comments may be used as if the
configuration file was normal Verilog code.

Note that file or line-specific configuration only applies to files read
after the configuration file. It is therefore recommended to pass the
configuration file to Verilator as the first file.

The grammar of configuration commands is as follows:

.. option:: `verilator_config

   Take remaining text and treat it as Verilator configuration commands.

.. option:: coverage_on  [-file "<filename>" [-lines <line> [ - <line> ]]]

.. option:: coverage_off [-file "<filename>" [-lines <line> [ - <line> ]]]

   Enable/disable coverage for the specified filename (or wildcard with
   '\*' or '?', or all files if omitted) and range of line numbers (or all
   lines if omitted).  Often used to ignore an entire module for coverage
   analysis purposes.

.. option:: clock_enable -module "<modulename>" -var "<signame>"

   Indicate the signal is used to gate a clock, and the user takes
   responsibility for insuring there are no races related to it.

   Same as :option:`/*verilator&32;clock_enable*/` metacomment.

.. option:: clocker -module "<modulename>" [-task "<taskname>"] -var "<signame>"

.. option:: clocker -module "<modulename>" [-function "<funcname>"] -var "<signame>"

.. option:: no_clocker -module "<modulename>" [-task "<taskname>"] -var "<signame>"

.. option:: no_clocker -module "<modulename>" [-function "<funcname>"] -var "<signame>"

   Indicates that the signal is used as clock or not. This information is
   used by Verilator to mark the signal and any derived signals as
   clocker.  See :vlopt:`--clk`.

   Same as :option:`/*verilator&32;clocker*/` metacomment.

.. option:: coverage_block_off -module "<modulename>" -block "<blockname>"

.. option:: coverage_block_off -file "<filename>" -line <lineno>

   Specifies the entire begin/end block should be ignored for coverage
   analysis purposes.  Can either be specified as a named block or as a
   filename and line number.

   Same as :option:`/*verilator&32;coverage_block_off*/` metacomment.

.. option:: forceable -module "<modulename>" -var "<signame>"

   Generate public `<signame>__VforceEn` and `<signame>__VforceVal` signals
   that can be used to force/release a signal from C++ code. The force control
   signals are created as :option:`public_flat` signals.

   Same as :option:`/*verilator&32;forceable*/` metacomment.

.. option:: full_case -file "<filename>" -lines <lineno>

.. option:: parallel_case -file "<filename>" -lines <lineno>

   Same as :code:`//synopsys full_case` and :code:`//synopsys
   parallel_case`. When these synthesis directives are discovered,
   Verilator will either formally prove the directive to be true, or
   failing that, will insert the appropriate code to detect failing cases
   at simulation runtime and print an "Assertion failed" error message.

.. option:: hier_block -module "<modulename>"

   Specifies that the module is a unit of hierarchical Verilation.  Note
   that the setting is ignored unless the :vlopt:`--hierarchical` option is
   specified.  See :ref:`Hierarchical Verilation`.

.. option:: inline -module "<modulename>"

   Specifies the module may be inlined into any modules that use this
   module.  Same as :option:`/*verilator&32;inline_module*/` metacomment.

.. option:: isolate_assignments -module "<modulename>" [-task "<taskname>"] -var "<signame>"

.. option:: isolate_assignments -module "<modulename>" [-function "<funcname>"] -var "<signame>"

.. option:: isolate_assignments -module "<modulename>" -function "<fname>"

   Used to indicate the assignments to this signal in any blocks should be
   isolated into new blocks.  When there is a large combinatorial block
   that is resulting in an UNOPTFLAT warning, attaching this to the signal
   causing a false loop may clear up the problem.

   Same as :option:`/*verilator&32;isolate_assignments*/` metacomment.

.. option:: no_inline -module "<modulename>"

   Specifies the module should not be inlined into any modules that use
   this module.  Same as :option:`/*verilator&32;no_inline_module*/`
   metacomment.

.. option:: no_inline [-module "<modulename>"] -task "<taskname>"

.. option:: no_inline [-module "<modulename>"] -function "<funcname>"

   Specify the function or task should not be inlined into where it is
   used.  This may reduce the size of the final executable when a task is
   used a very large number of times.  For this flag to work, the task and
   tasks below it must be pure; they cannot reference any variables outside
   the task itself.

   Same as :option:`/*verilator&32;no_inline_task*/` metacomment.

.. option:: lint_on  [-rule <message>] [-file "<filename>" [-lines <line> [ - <line>]]]

.. option:: lint_off [-rule <message>] [-file "<filename>" [-lines <line> [ - <line>]]]

.. option:: lint_off [-rule <message>] [-file "<filename>"] [-match "<string>"]

   Enable/disables the specified lint warning, in the specified filename
   (or wildcard with '\*' or '?', or all files if omitted) and range of
   line numbers (or all lines if omitted).

   With lint_off using "\*" will override any lint_on directives in the
   source, i.e. the warning will still not be printed.

   If the -rule is omitted, all lint warnings (see list in
   :vlopt:`-Wno-lint`) are enabled/disabled.  This will override all later
   lint warning enables for the specified region.

   If -match is set the linter warnings are matched against this (wildcard)
   string and are waived in case they match and iff rule and file (with
   wildcard) also match.

   In previous versions -rule was named -msg. The latter is deprecated, but
   still works with a deprecation info, it may be removed in future
   versions.

.. option:: public [-module "<modulename>"] [-task/-function "<taskname>"]  -var "<signame>"

.. option:: public_flat [-module "<modulename>"] [-task/-function "<taskname>"]  -var "<signame>"

.. option:: public_flat_rd [-module "<modulename>"] [-task/-function "<taskname>"]  -var "<signame>"

.. option:: public_flat_rw [-module "<modulename>"] [-task/-function "<taskname>"]  -var "<signame>" "@(edge)"

   Sets the variable to be public.  Same as
   :option:`/*verilator&32;public*/` or
   :option:`/*verilator&32;public_flat*/`, etc, metacomments. See
   e.g. :ref:`VPI Example`.

.. option:: profile_data -mtask "<mtask_hash>" -cost <cost_value>

   Feeds profile-guided optimization data into the Verilator algorithms in
   order to improve model runtime performance.  This option is not expected
   to be used by users directly.  See :ref:`Thread PGO`.

.. option:: sc_bv -module "<modulename>" [-task "<taskname>"] -var "<signame>"

.. option:: sc_bv -module "<modulename>" [-function "<funcname>"] -var "<signame>"

   Sets the port to be of :code:`sc_bv<{width}>` type, instead of bool,
   uint32_t or uint64_t.  Same as :option:`/*verilator&32;sc_bv*/`
   metacomment.

.. option:: sformat [-module "<modulename>"] [-task "<taskname>"] -var "<signame>"

.. option:: sformat [-module "<modulename>"] [-function "<funcname>"] -var "<signame>"

   Must be applied to the final argument of type :code:`input string` of a
   function or task to indicate the function or task should pass all
   remaining arguments through $sformatf.  This allows creation of DPI
   functions with $display like behavior.  See the
   :file:`test_regress/t/t_dpi_display.v` file for an example.

   Same as :option:`/*verilator&32;sformat*/` metacomment.

.. option:: split_var [-module "<modulename>"] [-task "<taskname>"] -var "<varname>"

.. option:: split_var [-module "<modulename>"] [-function "<funcname>"] -var "<varname>"

   Break the variable into multiple pieces typically to resolve UNOPTFLAT
   performance issues. Typically the variables to attach this to are
   recommended by Verilator itself, see :option:`UNOPTFLAT`.

   Same as :option:`/*verilator&32;split_var*/` metacomment.

.. option:: tracing_on  [-file "<filename>" [-lines <line> [ - <line> ]]]

.. option:: tracing_off [-file "<filename>" [-lines <line> [ - <line> ]]]

.. option:: tracing_on  [-scope "<scopename>" [-levels <levels> ]]

.. option:: tracing_off [-scope "<scopename>" [-levels <levels> ]]

   Enable/disable waveform tracing for all future signals declared in
   all files.

   With -file, enable/disable waveform tracing in the specified
   filename (or wildcard with '\*' or '?'), and -line range of line
   numbers (or all lines if omitted).

   For tracing_off with -file, instances below any module in the
   files/ranges specified will also not be traced.  To overcome this
   feature, use tracing_on on the upper module declaration and on any
   cells, or use the -scope flavor of the command.

   With -scope enable/disable waveform tracing for the specified scope (or
   wildcard with '\*' or '?'), and optional --levels number of levels
   below.  These controls only take place after other file/line/module
   based controls have indicated the signal should be traced.

   With -levels (used with -scope), the number of levels below that
   scope which the rule is to match, where 0 means all levels below, 1
   the exact level as the provided scope, and 2 meaning an additional
   level of children below the provided scope, etc.
