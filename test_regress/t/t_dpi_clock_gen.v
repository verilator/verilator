// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2021 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module testbench;

   logic clk;

   export "DPI-C" function set_clk;
   function void set_clk(bit val);
      clk = val;
   endfunction;

   // Downstream signal dependent on clk demonstrates scheduling issue.
   wire  gated_clk;
   assign gated_clk = $c1("1") & clk;

   int   n = 0;

   always @(posedge gated_clk) begin
      $display("n=%d", n);
      if (n == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      n += 1;
   end

endmodule

