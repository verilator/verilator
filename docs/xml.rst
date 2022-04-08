|Logo|

***************************
Verilator XML Output Format
***************************

Introduction
============

This document describes Verilator's XML output. For more general
information please see `verilator.org <https://verilator.org>`__.


General
=======

Verilator's XML output is enabled with the ``--xml-only`` flag. It contains
limited information about the elaborated design including files, modules,
instance hierarchy, logic and data types. There is no formal schema since
part of the structure of the XML document matches the compiled code which
would require the schema to describe legal SystemVerilog structure. The
intended usage is to enable other downstream tools to take advantage of
Verilator's parser.


Structure
=========

The XML document consists of 4 sections within the top level
``verilator_xml`` element:

``<files>``\ ... ``</files>``
   This section contains a list of all design files read, including the
   built-in constructs and the command line as their own entries. Each
   ``<file>`` has an attribute ``id`` which is a short ASCII string
   unique to that file. Other elements' ``loc`` attributes use this id
   to refer to a particular file.

``<module_files>``\ ... ``</module_files>``
   All files containing Verilog module definitions are listed in this
   section. This element's contents is a subset of the ``<files>``
   element's contents.

``<cells>``\ ... ``</cells>``
   The cells section of the XML document contains the design instance
   hierarchy. Each instance is represented with the ``<cell>`` element
   with the following attributes:

   -  ``loc``: The file id, first line number, last line number, first
      column number and last column number of the identifier where the
      module was instanced, separated by commas.

   -  ``name``: The instance name.

   -  ``submodname``: The module name uniquified with particular
      parameter values (if any).

   -  ``hier``: The full hierarchy path.

``<netlist>``\ ... ``</netlist>``
   The netlist section contains a number of
   ``<module>``\ ... ``</module>`` elements, each describing the
   contents of that module, and a single ``<typetable>``\ ...
   ``</typetable>`` element which lists all used types used within the
   modules. Each type has a numeric ``id`` attribute that is referred to
   by elements in the ``<module>`` elements using the ``dtype_id``
   attribute.


Distribution
============

Copyright 2020-2022 by Wilson Snyder. Verilator is free software; you can
redistribute it and/or modify it under the terms of either the GNU Lesser
General Public License Version 3 or the Perl Artistic License Version 2.0.

.. |Logo| image:: https://www.veripool.org/img/verilator_256_200_min.png
