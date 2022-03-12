.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

First you need Verilator installed, see :ref:`Installation`. In brief, if
you installed Verilator using the package manager of your operating system,
or did a :command:`make install` to place Verilator into your default path,
you do not need anything special in your environment, and should not have
VERILATOR_ROOT set.  However, if you installed Verilator from sources and
want to run Verilator out of where you compiled Verilator, you need to
point to the kit:

.. code-block:: bash

     # See above; don't do this if using an OS-distributed Verilator
     export VERILATOR_ROOT=/path/to/where/verilator/was/installed
     export PATH=$VERILATOR_ROOT/bin:$PATH
