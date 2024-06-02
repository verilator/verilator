// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   parameter integer BLKS = 3;

   generate
      for (genvar blkIdx=0; blkIdx < BLKS; blkIdx=blkIdx+1 ) begin : slice

         import "DPI-C" context function void dpi_genvarTest ();

         initial begin
            dpi_genvarTest();
            $display("slice = %0d   :  %m", blkIdx);
         end
     end
   endgenerate

   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
