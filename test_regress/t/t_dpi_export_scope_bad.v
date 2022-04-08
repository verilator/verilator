// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;
   s s();

   import "DPI-C" context function void dpix_run_tests();
   initial dpix_run_tests();
endmodule

module s;
   export "DPI-C" task dpix_task;
   task dpix_task();
      $write("Hello in %m\n");
   endtask
endmodule
