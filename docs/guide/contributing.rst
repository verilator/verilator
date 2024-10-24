.. Copyright 2003-2024 by Wilson Snyder.
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
the bug (see: :ref:`Minimizing bug-inducing code`).  Even better, create
a test in the :file:`test_regress/t` directory, as follows:

.. code-block:: bash

       cd test_regress
       cp -p t/t_EXAMPLE.py t/t_BUG.py
       cp -p t/t_EXAMPLE.v t/t_BUG.v

There are many hints on how to write a good test in the
:file:`test_regress/driver.py` documentation which can be seen by running:

.. code-block:: bash

       cd $VERILATOR_ROOT  # Need the original distribution kit
       test_regress/driver.py --help

Edit :file:`t/t_BUG.py` to suit your example; you can do anything you want
in the Verilog code there; just make sure it retains the single clk input
and no outputs.  Now, the following should fail:

.. code-block:: bash

       cd $VERILATOR_ROOT  # Need the original distribution kit
       cd test_regress
       t/t_BUG.py  # Run on Verilator
       t/t_BUG.py --debug # Run on Verilator, passing --debug to Verilator
       t/t_BUG.py --vcs  # Run on VCS simulator
       t/t_BUG.py --nc|--iv|--ghdl  # Likewise on other simulators

The test driver accepts a number of options, many of which mirror the main
Verilator options. For example the previous test could have been run with
debugging enabled.  The full set of test options can be seen by running
:command:`driver.py --help` as shown above.

Finally, report the bug at `Verilator Issues
<https://verilator.org/issues>`_.  The bug will become publicly visible; if
this is unacceptable, mail the bug report to ``wsnyder@wsnyder.org``.

Minimizing bug-inducing code
============================

In some cases, the part of the code that causes the bug is clearly visible
and the design can be easily manually reduced. In other cases, the bug is
caused by a complex interaction of many parts of the design, and it is not
clear which parts are necessary to reproduce the bug. In these cases, an
Open Source tool called `sv-bugpoint
<https://github.com/antmicro/sv-bugpoint>_` can be used to automatically
reduce a SystemVerilog design to the smallest possible reproducer.
It can be used to automatically reduce a design with hundreds of thousands of
lines to a minimal test case while preserving the bug-inducing behavior.

Please refer to the `README
<https://github.com/antmicro/sv-bugpoint/blob/main/README.md>`_ file for more
information on how to use `sv-bugpoint`.

.. Contributing
.. ============
.. include:: ../CONTRIBUTING.rst
