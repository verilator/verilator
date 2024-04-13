.. Github doesn't render images unless absolute URL
.. Do not know of a conditional tag, "only: github" nor "github display" works

|badge1| |badge2| |badge3| |badge4| |badge5| |badge6| |badge7| |badge8|

.. |badge1| image:: https://img.shields.io/badge/Website-Verilator.org-181717.svg
    :target: https://verilator.org
.. |badge2| image:: https://img.shields.io/badge/License-LGPL%20v3-blue.svg
    :target: https://www.gnu.org/licenses/lgpl-3.0
.. |badge3| image:: https://img.shields.io/badge/License-Artistic%202.0-0298c3.svg
    :target: https://opensource.org/licenses/Artistic-2.0
.. |badge4| image:: https://repology.org/badge/tiny-repos/verilator.svg?header=distro%20packages
    :target: https://repology.org/project/verilator/versions
.. |badge5| image:: https://img.shields.io/docker/pulls/verilator/verilator
    :target: https://hub.docker.com/r/verilator/verilator
.. |badge6| image:: https://api.codacy.com/project/badge/Grade/fa78caa433c84a4ab9049c43e9debc6f
    :target: https://www.codacy.com/gh/verilator/verilator
.. |badge7| image:: https://codecov.io/gh/verilator/verilator/branch/master/graph/badge.svg
    :target: https://codecov.io/gh/verilator/verilator
.. |badge8| image:: https://github.com/verilator/verilator/workflows/build/badge.svg
    :target: https://github.com/verilator/verilator/actions?query=workflow%3Abuild


Welcome to Verilator
====================

.. list-table::

   * - **Welcome to Verilator, the fastest Verilog/SystemVerilog simulator.**
        * Accepts Verilog or SystemVerilog
        * Performs lint code-quality checks
        * Compiles into multithreaded C++, or SystemC
        * Creates XML to front-end your own tools
     - |Logo|
   * - |verilator multithreaded performance|
     - **Fast**
        * Outperforms many closed-source commercial simulators
        * Single- and multithreaded output models
   * - **Widely Used**
        * Wide industry and academic deployment
        * Out-of-the-box support from Arm and RISC-V vendor IP
     - |verilator usage|
   * - |verilator community|
     - **Community Driven & Openly Licensed**
        * Guided by the `CHIPS Alliance`_ and `Linux Foundation`_
        * Open, and free as in both speech and beer
        * More simulation for your verification budget
   * - **Commercial Support Available**
        * Commercial support contracts
        * Design support contracts
        * Enhancement contracts
     - |verilator support|


What Verilator Does
===================

Verilator is invoked with parameters similar to GCC or Synopsys's VCS.  It
"Verilates" the specified Verilog or SystemVerilog code by reading it,
performing lint checks, and optionally inserting assertion checks and
coverage-analysis points. It outputs single- or multithreaded .cpp and .h
files, the "Verilated" code.

These Verilated C++/SystemC files are then compiled by a C++ compiler
(gcc/clang/MSVC++), optionally along with a user's own C++/SystemC wrapper
file, to instantiate the Verilated model. Executing the resulting
executable performs the design simulation. Verilator also supports linking
Verilated generated libraries, optionally encrypted, into other simulators.

Verilator may not be the best choice if you are expecting a full-featured
replacement for a closed-source Verilog simulator, need SDF annotation,
mixed-signal simulation, or are doing a quick class project (we recommend
`Icarus Verilog`_ for classwork).  However, if you are looking for a path
to migrate SystemVerilog to C++/SystemC, or want high-speed simulation of
designs, Verilator is the tool for you.


Performance
===========

Verilator does not directly translate Verilog HDL to C++ or SystemC. Rather,
Verilator compiles your code into a much faster optimized and optionally
thread-partitioned model, which is in turn wrapped inside a C++/SystemC
module. The results are a compiled Verilog model that executes even on a
single thread over 10x faster than standalone SystemC, and on a single
thread is about 100 times faster than interpreted Verilog simulators such
as `Icarus Verilog`_. Another 2-10x speedup might be gained from
multithreading (yielding 200-1000x total over interpreted simulators).

Verilator has typically similar or better performance versus
closed-source Verilog simulators (e.g., Carbon Design Systems Carbonator,
Modelsim/Questa, Cadence Incisive/NC-Verilog, Synopsys VCS, VTOC, and
Pragmatic CVer/CVC). But, Verilator is open-sourced, so you can spend on
computes rather than licenses. Thus, Verilator gives you the best
simulation cycles/dollar.


Installation & Documentation
============================

For more information:

- `Verilator installation and package directory structure
  <https://verilator.org/install>`_

- `Verilator manual (HTML) <https://verilator.org/verilator_doc.html>`_,
  or `Verilator manual (PDF) <https://verilator.org/verilator_doc.pdf>`_

- `Subscribe to Verilator announcements
  <https://github.com/verilator/verilator-announce>`_

- `Verilator forum <https://verilator.org/forum>`_

- `Verilator issues <https://verilator.org/issues>`_


Support
=======

Verilator is a community project, guided by the `CHIPS Alliance`_ under the
`Linux Foundation`_.

We appreciate and welcome your contributions in whatever form; please see
`Contributing to Verilator
<https://github.com/verilator/verilator/blob/master/docs/CONTRIBUTING.rst>`_.
Thanks to our `Contributors and Sponsors
<https://verilator.org/guide/latest/contributors.html>`_.

Verilator also supports and encourages commercial support models and
organizations; please see `Verilator Commercial Support
<https://verilator.org/verilator_commercial_support>`_.


Related Projects
================

- `GTKwave <http://gtkwave.sourceforge.net/>`_ - Waveform viewer for
  Verilator traces.

- `Icarus Verilog`_ - Icarus is a full-featured interpreted Verilog
  simulator. If Verilator does not support your needs, perhaps Icarus may.


Open License
============

Verilator is Copyright 2003-2024 by Wilson Snyder. (Report bugs to
`Verilator Issues <https://verilator.org/issues>`_.)

Verilator is free software; you can redistribute it and/or modify it under
the terms of either the GNU Lesser General Public License Version 3 or the
Perl Artistic License Version 2.0. See the documentation for more details.

.. _CHIPS Alliance: https://chipsalliance.org
.. _Icarus Verilog: https://steveicarus.github.io/iverilog
.. _Linux Foundation: https://www.linuxfoundation.org
.. |Logo| image:: https://www.veripool.org/img/verilator_256_200_min.png
.. |verilator multithreaded performance| image:: https://www.veripool.org/img/verilator_multithreaded_performance_bg-min.png
.. |verilator usage| image:: https://www.veripool.org/img/verilator_usage_400x200-min.png
.. |verilator community| image:: https://www.veripool.org/img/verilator_community_400x125-min.png
.. |verilator support| image:: https://www.veripool.org/img/verilator_support_400x125-min.png
