.. Copyright 2003-2024 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _Example Create-Binary Execution:

Example Create-Binary Execution
===============================

We'll compile this SystemVerilog example into a Verilated simulation binary.  For
an example that discusses the next level of detail see :ref:`Example C++
Execution`.

.. include:: example_common_install.rst

Now, let's create an example Verilog file:

.. code-block:: bash

     mkdir test_our
     cd test_our

     cat >our.v <<'EOF'
       module our;
          initial begin $display("Hello World"); $finish; end
       endmodule
     EOF

Now we run Verilator on our little example.

.. code-block:: bash

     verilator --binary -j 0 -Wall our.v

Breaking this command down:

#. :vlopt:`--binary` telling Verilator to do everything needed to create a
   simulation executable.

#. :vlopt:`-j` `0` to Verilate using use as many CPU threads as the machine
   has.

#. :vlopt:`-Wall` so Verilator has stronger lint warnings
   enabled.

#. An finally, :command:`our.v`, which is our SystemVerilog design file.

And now we run it:

.. code-block:: bash

     obj_dir/Vour

And we get as output:

.. code-block:: bash

     Hello World
     - our.v:2: Verilog $finish

You're better off using a Makefile to run the steps for you, so when your
source changes, it will automatically run all of the appropriate steps.  To
aid this, Verilator can create a makefile dependency file.  For examples
that do this, see the :file:`examples` directory in the distribution.
