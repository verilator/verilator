// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t_format_wide_decimal(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int   cycle = 0;
   bit [1023:0] x = '1;

   always @(posedge clk) begin
      if (cycle == 0) begin
         // Format very wide constant number (which has more bits than can
         // be counted in exponent of a double precision float), with %d.
         $display("%d", 1024'hffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
      end else begin
         // Same, but for a variable with value only known at run-time
         $display("%d", x);
      end

      cycle <= cycle + 1;
      x <= x >> 1;

      if (cycle == 2) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
