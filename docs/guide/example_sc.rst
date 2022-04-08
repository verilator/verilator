.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _Example SystemC Execution:

Example SystemC Execution
=========================

This is an example similar to the :ref:`Example C++ Execution`, but using
SystemC. We'll also explicitly run make.

.. include:: example_common_install.rst

Now, let's create an example Verilog, and SystemC wrapper file:

.. code-block:: bash

     mkdir test_our_sc
     cd test_our_sc

     cat >our.v <<'EOF'
       module our (clk);
          input clk;  // Clock is required to get initial activation
          always @(posedge clk)
             begin $display("Hello World"); $finish; end
       endmodule
     EOF

     cat >sc_main.cpp <<'EOF'
       #include "Vour.h"
       int sc_main(int argc, char** argv) {
           Verilated::commandArgs(argc, argv);
           sc_clock clk{"clk", 10, SC_NS, 0.5, 3, SC_NS, true};
           Vour* top = new Vour{"top"};
           top->clk(clk);
           while (!Verilated::gotFinish()) { sc_start(1, SC_NS); }
           delete top;
           return 0;
       }
     EOF

Now we run Verilator on our little example:

.. code-block:: bash

     verilator -Wall --sc --exe sc_main.cpp our.v

This example does not use --build, therefore we need to explicitly compile
it:

.. code-block:: bash

     make -j -C obj_dir -f Vour.mk Vour

And now we run it:

.. code-block:: bash

     obj_dir/Vour

And we get, after the SystemC banner, the same output as the C++ example:

.. code-block:: bash

     SystemC 2.3.3-Accellera

     Hello World
     - our.v:4: Verilog $finish

Really, you're better off using a Makefile to run the steps for you so when
your source changes it will automatically run all of the appropriate steps.
For examples that do this see the :file:`examples` directory in the
distribution.
