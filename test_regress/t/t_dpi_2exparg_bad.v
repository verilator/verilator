// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module a;
   import "DPI-C" task dpii_twice;  // Legal
   export "DPI-C" task dpix_twice;  // Bad
   task dpix_twice(input int i, output [2:0] o);  o = ~i; endtask
   initial dpii_twice();
endmodule

module b;
   import "DPI-C" task dpii_twice;  // Legal
   export "DPI-C" task dpix_twice;  // Bad
   task dpix_twice(input int i, output [63:0] o);  o = ~i; endtask
   initial dpii_twice();
endmodule

module t;
   a a();
   b b();

   initial begin
      $stop;
   end
endmodule
