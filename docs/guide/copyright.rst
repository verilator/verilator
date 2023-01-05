.. Copyright 2003-2023 by Wilson Snyder.
.. SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

*********
Copyright
*********

The latest version of Verilator is available from `https://verilator.org
<https://verilator.org>`_.

Copyright 2003-2023 by Wilson Snyder. This program is free software; you
can redistribute it and/or modify the Verilator internals under the terms
of either the GNU Lesser General Public License Version 3 or the Perl
Artistic License Version 2.0.

All Verilog and C++/SystemC code quoted within this documentation file is
released as Creative Commons Public Domain (CC0). Many example files and
test files are likewise released under CC0 into effectively the Public
Domain as described in the files themselves.

   Warns that the lifetime of a task or a function was not provided and so
   was implicitly set to static. The warning is suppressed when no
   variables inside the task or a function are assigned to.

   This is a warning because the static default differs from C++, differs
   from class member function/tasks.  Static is a more dangerous default
   then automatic as static prevents the function from being reinterant,
   which may be a source of bugs, and/or performance issues.

   If the function does not require static behavior, change it to "function
   automatic".

   If the function requires static behavior, change it to "function
   static".

   Ignoring this warning will only suppress the lint check; it will
   simulate correctly.
