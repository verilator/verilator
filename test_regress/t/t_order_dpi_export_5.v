// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2021 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module testbench(
                 /*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cnt = 0;
   export "DPI-C" function set_cnt;
   function void set_cnt(int val);
      cnt = val;
   endfunction;
   export "DPI-C" function get_cnt;
   function int get_cnt();
      return cnt;
   endfunction;

   always @(posedge clk) cnt += 1;

   // Downstream combinational signal dependent on both input clock and
   // DPI export.
   wire  dependent_clk = cnt == 2;

   int   n = 0;

   always @(posedge dependent_clk) begin
      $display("t=%t n=%d", $time, n);
      if ($time != (8*n+3) * 500) $stop;
      if (n == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      n += 1;
   end

endmodule
