.. Copyright 2003-2025 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

verilator_coverage
==================

Verilator_coverage processes Verilated model-generated coverage reports.

With `--annotate`, it reads the specified coverage data file and generates
annotated source code with coverage metrics annotated.  With
`--annotate-points` the coverage points corresponding to each line are also
shown.

Additional Verilog-XL-style standard arguments specify the search paths
necessary to find the source code on which the coverage analysis was
performed.

To filter those items to be included in coverage, you may read
logs/coverage.dat into an editor and do a M-x keep-lines to include only
those statistics of interest and save to a new .dat file.

For Verilog conditions that should never occur, either add a $stop
statement to the appropriate statement block, or see
:option:`/*verilator&32;coverage_off*/`.  This will remove the coverage
points after the model is re-Verilated.

For an overview of the use of verilator_coverage, see :ref:`Coverage Analysis`.


verilator_coverage Example Usage
--------------------------------

..

    verilator_coverage --help
    verilator_coverage --version

    verilator_coverage --annotate obj_dir coverage.dat

    verilator_coverage --write merged.dat coverage.dat ...

    verilator_coverage --write-info merged.info coverage.dat ...


verilator_coverage Arguments
----------------------------

.. program:: verilator_coverage

.. option:: <filename>

   Specifies the input coverage data file.  Multiple filenames may be
   provided to read multiple inputs.  If no data file is specified, by
   default, "coverage.dat" will be read.

.. option:: --annotate <output_directory>

   Specifies the directory name to which source files with annotated
   coverage data should be written.

   Points are children of each line coverage- branches, expressions or
   toggle points.  When point counts are aggregated into a line, the
   minimum and maximum counts are used to determine the status of the line
   (complete, partial, failing) The count is equal to the maximum of the
   points.

   Coverage data is annotated at the beginning of the line and is formatted
   as a special character followed by the number of coverage hits. The
   special characters " ,%,~,+,-" indicate summary of the coverage, and
   allow use of grep to filter the report.

   * " " (whitespace) indicates that all points on the line are above the coverage min.
   * "%" indicates that all points on the line are below the coverage min.
   * "~" indicates that some points on the line are above the coverage min and some are below.
   * "+" coverage point was at or above the min. Only used with :option:`--annotate-points`.
   * "-" coverage point was below the min.  Only used with :option:`--annotate-points`.

   .. code-block::

      100000  input logic a;      // Begins with whitespace, because
                                  // number of hits (100000) is above the min.
     +100000  point: comment=a    // Begins with +, because
                                  // number of hits (100000) is above the min.
     %000000  input logic b;      // Begins with %, because
                                  // number of hits (0) is below the min.
     -000000  point: comment=b    // Begins with -, because
                                  // number of hits (0) is below the min.
     ~000010  if (cyc!=0) begin   // Begins with ~, because
                                  // branches are below and above the min.
     +000010  point: comment=if   // The if branch is above the min.
     -000000  point: comment=else // The else branch is below the min.

.. option:: --annotate-all

   Specifies all files should be shown.  By default, only those source
   files with low coverage are written to the output directory.

   This option should be used together with :option:`--annotate`.

.. option:: --annotate-min <count>

   Specifies the threshold (<count>) below which coverage point is
   considered sufficient. If the threshold is not exceeded, then the
   annotation will begin with a "%" symbol to indicate the coverage is
   insufficient.

   The <count> threshold defaults to 10.

   This option should be used together with :option:`--annotate`.


.. option:: --annotate-points

   Specifies all coverage points should be shown after each line of text.  By
   default, only source lines are shown.

   .. code-block::

     100000  input logic a, b, c;
    +100000 point: comment=a  // These lines are only shown
    +200000 point: comment=b  // with option --annotate-points
    +300000 point: comment=c  // enabled.


   This option should be used together with :option:`--annotate`.

.. option:: --filter-type <type>

   Skips records of coverage types different than <type>.
   Possible values are `toggle`, `line`, `branch`, `expr`, `user`.

.. option:: --help

   Displays a help summary, the program version, and exits.

.. option:: --rank

   Prints an experimental report listing the relative importance of each
   test in covering all of the coverage points.  The report shows "Covered"
   which indicates the number of points the test covers; a test is
   considered to cover a point if it has a bucket count of at least 1. The
   "rank" column has a higher number t indicate the test is more critical,
   and rank 0 means the test does not need to be run to cover the points.
   "RankPts" indicates the number of coverage points this test will
   contribute to overall coverage if all tests are run in the order of
   highest to the lowest rank.

.. option:: --unlink

   With :option:`--write`, unlink all input files after the output has been
   successfully created.

.. option:: --version

   Displays program version and exits.

.. option:: --write <filename>

   Specifies the aggregate coverage results, summed across all the files,
   should be written to the given filename in verilator_coverage data
   format.  This is useful in scripts to combine many coverage data files
   (likely generated from random test runs) into one master coverage file.

.. option:: --write-info <filename.info>

   Specifies the aggregate coverage results, summed across all the files,
   should be written to the given filename in :command:`lcov` .info format.
   This may be used to feed into :command:`lcov` to aggregate or generate
   reports. This format lacks the comments for cover points that the
   verilator_coverage format has. It can be used with :command:`genhtml` to
   generate an HTML report. :command:`genhtml --branch-coverage` will also
   display the branch coverage, analogous to :option:`--annotate-points`.
