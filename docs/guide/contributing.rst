.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

*******************************
Contributing and Reporting Bugs
*******************************

Announcements
=============

To get notified of new releases and other important announcements, go to
`Verilator announcement repository
<https://github.com/verilator/verilator-announce>`__ and follow the
instructions there.


Reporting Bugs
==============

First, check the :ref:`Language Limitations` section.

Next, try the :vlopt:`--debug` option.  This will enable additional
internal assertions, and may help identify the problem.

Finally, reduce your code to the smallest possible routine that exhibits
the bug.  Even better, create a test in the :file:`test_regress/t`
directory, as follows:

.. code-block:: bash

       cd test_regress
       cp -p t/t_EXAMPLE.pl t/t_BUG.pl
       cp -p t/t_EXAMPLE.v t/t_BUG.v

There are many hints on how to write a good test in the
:file:`test_regress/driver.pl` documentation which can be seen by running:

.. code-block:: bash

       cd $VERILATOR_ROOT  # Need the original distribution kit
       test_regress/driver.pl --help

Edit :file:`t/t_BUG.pl` to suit your example; you can do anything you want
in the Verilog code there; just make sure it retains the single clk input
and no outputs.  Now, the following should fail:

.. code-block:: bash

       cd $VERILATOR_ROOT  # Need the original distribution kit
       cd test_regress
       t/t_BUG.pl  # Run on Verilator
       t/t_BUG.pl --debug # Run on Verilator, passing --debug to Verilator
       t/t_BUG.pl --vcs  # Run on VCS simulator
       t/t_BUG.pl --nc|--iv|--ghdl  # Likewise on other simulators

The test driver accepts a number of options, many of which mirror the main
Verilator options. For example the previous test could have been run with
debugging enabled.  The full set of test options can be seen by running
:command:`driver.pl --help` as shown above.

Finally, report the bug at `Verilator Issues
<https://verilator.org/issues>`_.  The bug will become publicly visible; if
this is unacceptable, mail the bug report to ``wsnyder@wsnyder.org``.


.. Contributing
.. ============
.. include:: ../CONTRIBUTING.rst
