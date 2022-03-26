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

   input clk; // Top level input clock
   logic other_clk; // Dependent clock set via DPI

   export "DPI-C" function set_other_clk;
   function void set_other_clk(bit val);
      other_clk = val;
   endfunction;

   bit even_other = 1;
   import "DPI-C" context function void toggle_other_clk(bit val);
   always @(posedge clk) begin
     even_other <= ~even_other;
     toggle_other_clk(even_other);
   end

   int   n = 0;

   always @(posedge other_clk) begin
      $display("t=%t n=%d", $time, n);
      if ($time != (4*n+1) * 500) $stop;
      if (n == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      n += 1;
   end

endmodule
