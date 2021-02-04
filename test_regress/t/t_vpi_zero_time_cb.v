// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

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
   end

   always @(posedge clk) begin
`ifdef TEST_VERBOSE
      $display("[%0t] clk", $time);
`endif
      count <= count + 2;
      if (count == 1000) begin
         // See C++ code: $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule : t
