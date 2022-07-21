// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2022 by Geza Lore. This program is free software; you can
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

   bit x = 0;

   wire y = x & $c(1);

   export "DPI-C" function set_x;
   function void set_x(bit val);
      x = val;
   endfunction;

   import "DPI-C" context function void call_set_x(bit val);

   bit q = 0;
   always @(posedge clk) q <= ~q;

   always @(edge q) call_set_x(q);

   int n = 0;

   always @(edge clk) begin
      // This always block needs to evaluate before the NBA to even_other
      // above is committed, as setting clocks via the set_other_clk uses
      // blocking assignment.
      $display("t=%t q=%d x=%d y=%d", $time, q, x, y);
      if (y !== q) $stop;
      if (n == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      n += 1;
   end

endmodule
