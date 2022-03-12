.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

verilator_coverage
==================

Verilator_coverage processes Verilated model-generated coverage reports.

With --annotate, it reads the specified coverage data file and generates
annotated source code with coverage metrics annotated.  If multiple
coverage points exist on the same source code line, additional lines will
be inserted to report the additional points.

Additional Verilog-XL-style standard arguments specify the search paths
necessary to find the source code that the coverage analysis was performed
on.

To filter those items to be included in coverage, you may read
logs/coverage.dat into an editor and do a M-x keep-lines to include only
those statistics of interest and save to a new .dat file.

For Verilog conditions that should never occur, either add a $stop
statement to the appropriate statement block, or see
:option:`/*verilator&32;coverage_off*/`.  This will remove the coverage
points after the model is re-Verilated.

For an overview of use of verilator_coverage, see :ref:`Coverage Analysis`.


verilator_coverage Example Usage
--------------------------------

..

    verilator_coverage --help
    verilator_coverage --version

    verilator_coverage --annotate <obj>

    verilator_coverage  -write merged.dat -read <datafiles>...

    verilator_coverage  -write-info merged.info -read <datafiles>...


verilator_coverage Arguments
----------------------------

.. program:: verilator_coverage

.. option:: <filename>

Specifies the input coverage data file.  Multiple filenames may be provided
to read multiple inputs.  If no data file is specified, by default
"coverage.dat" will be read.

.. option:: --annotate <output_directory>

Specifies the directory name that source files with annotated coverage data
should be written to.

.. option:: --annotate-all

Specifies all files should be shown.  By default, only those source files
which have low coverage are written to the output directory.

.. option:: --annotate-min <count>

Specifies if the coverage point does not include the count number of
coverage hits, then the coverage point will be considered above the
threshold, and the coverage report will put a "%" to indicate the coverage
is not sufficient.  Defaults to 10.

.. option:: --help

Displays a help summary, the program version, and exits.

.. option:: --rank

Prints an experimental report listing the relative importance of each test
in covering all of the coverage points.  The report shows "Covered" which
indicates the number of points that test covers; a test is considered to
cover a point if it has a bucket count of at least 1. The "rank" column has
a higher number t indicate the test is more important, and rank 0 means the
test does not need to be run to cover the points.  "RankPts" indicates the
number of coverage points this test will contribute to overall coverage if
all tests are run in the order of highest to lowest rank.

.. option:: --unlink

With :option:`--write`, unlink all input files after the output
has been successfully created.

.. option:: --version

Displays program version and exits.

.. option:: --write <filename>

Specifies the aggregate coverage results, summed across all the files,
should be written to the given filename in verilator_coverage data format.
This is useful for use in scripts to combine many coverage data files
(likely generated from random test runs) into one master coverage file.

.. option:: --write-info <filename.info>

Specifies the aggregate coverage results, summed across all the files,
should be written to the given filename in :command:`lcov` .info format.
This may be used to feed into :command:`lcov` to aggregate or generate
reports.

The info format loses data compared to the Verilator coverage data format;
the info will all forms of coverage converted to line style coverage, and
if there are multiple coverage points on a single line, the minimum
coverage across those points will be used to report coverage of the line.
