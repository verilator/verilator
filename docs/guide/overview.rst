.. Copyright 2003-2022 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

********
Overview
********

Welcome to Verilator!

The Verilator package converts Verilog [#]_ and SystemVerilog [#]_ hardware
description language (HDL) designs into a C++ or SystemC model that after
compiling can be executed.  Verilator is not a traditional simulator, but a
compiler.

Verilator is typically used as follows:

1. The :command:`verilator` executable is invoked with parameters similar
to GCC, or other simulators such as Cadence Verilog-XL/NC-Verilog, or
Synopsys VCS.  Verilator reads the specified SystemVerilog code, lints it,
optionally adds coverage and waveform tracing support, and compiles the
design into a source level multithreaded C++ or SystemC "model".  The
resulting model's C++ or SystemC code is output as .cpp and .h files. This
is referred to as "Verilating" and the process is "to Verilate"; the output
is a "Verilated" model.

2. For simulation, a small user written C++ wrapper file is required, the
"wrapper".  This wrapper defines the C++ standard function "main()" which
instantiates the Verilated model as a C++/SystemC object.

3. The user C++ wrapper, the files created by Verilator, a "runtime
library" provided by Verilator, and if applicable SystemC libraries are
then compiled using a C++ compiler to create a simulation executable.

4. The resulting executable will perform the actual simulation, during
"simulation runtime".

5. If appropriately enabled, the executable may also generate waveform
traces of the design that may be viewed.  It may also create coverage
analysis data for post-analysis.

The best place to get started is to try the :ref:`Examples`.


.. [#] Verilog is defined by the `Institute of Electrical and Electronics
       Engineers (IEEE) Standard for Verilog Hardware Description
       Language`, Std. 1364, released in 1995, 2001, and 2005.  The
       Verilator documentation uses the shorthand e.g. "IEEE 1394-2005" to
       refer to the e.g. 2005 version of this standard.

.. [#] SystemVerilog is defined by the `Institute of Electrical and
       Electronics Engineers (IEEE) Standard for SystemVerilog - Unified
       Hardware Design, Specification, and Verification Language`, Standard
       1800, released in 2005, 2009, 2012, and 2017.  The Verilator
       documentation uses the shorthand e.g. "IEEE 1800-2017" to refer to
       the e.g. 2017 version of this standard.
