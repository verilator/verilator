.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

.. _Example C++ Execution:

Example C++ Execution
=====================

We'll compile this example into C++.  For an extended and commented version
of what this C++ code is doing, see
:file:`examples/make_tracing_c/sim_main.cpp` in the distribution.

.. include:: example_common_install.rst

Now, let's create an example Verilog, and C++ wrapper file:

.. code-block:: bash

     mkdir test_our
     cd test_our

     cat >our.v <<'EOF'
       module our;
          initial begin $display("Hello World"); $finish; end
       endmodule
     EOF

     cat >sim_main.cpp <<'EOF'
       #include "Vour.h"
       #include "verilated.h"
       int main(int argc, char** argv, char** env) {
           VerilatedContext* contextp = new VerilatedContext;
           contextp->commandArgs(argc, argv);
           Vour* top = new Vour{contextp};
           while (!contextp->gotFinish()) { top->eval(); }
           delete top;
           delete contextp;
           return 0;
       }
     EOF

Now we run Verilator on our little example.

.. code-block:: bash

     verilator -Wall --cc --exe --build sim_main.cpp our.v

Breaking this command down:

#. :vlopt:`-Wall` so Verilator has stronger lint warnings
   enabled.

#. :vlopt:`--cc` to get C++ output (versus e.g. SystemC
   or only linting).

#. :vlopt:`--exe`, along with our :command:`sim_main.cpp` wrapper file, so
   the build will create an executable instead of only a library.

#. :vlopt:`--build` so Verilator will call make itself. This is we don't
   need to manually call make as a separate step. You can also write your
   own compile rules, and run make yourself as we show in :ref:`Example
   SystemC Execution`.)

#. An finally, :command:`our.v` which is our SystemVerilog design file.

Once Verilator completes we can see the generated C++ code under the
:file:`obj_dir` directory.

.. code-block:: bash

     ls -l obj_dir

(See :ref:`Files Read/Written` for descriptions of some of the files that
were created.)

And now we run it:

.. code-block:: bash

     obj_dir/Vour

And we get as output:

.. code-block:: bash

     Hello World
     - our.v:2: Verilog $finish

Really, you're better off using a Makefile to run the steps for you so when
your source changes it will automatically run all of the appropriate steps.
To aid this Verilator can create a makefile dependency file.  For examples
that do this see the :file:`examples` directory in the distribution.
