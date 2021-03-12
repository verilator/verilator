// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import "DPI-C" function void dpii_init();
import "DPI-C" function void dpii_final();

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [31:0]      count        /*verilator public_flat_rd */;

   integer        status;

   // Test loop
   initial begin
      count = 0;
      dpii_init();
   end

   always @(posedge clk) begin
`ifdef TEST_VERBOSE
      $display("[%0t] clk @ count %0d", $time, count);
`endif
      count <= count + 2;
      if (count == 200) begin
         $display("Final section");
         // See C++ code: $write("*-* All Finished *-*\n");
         dpii_final();
         $finish;
      end
   end

endmodule : t
