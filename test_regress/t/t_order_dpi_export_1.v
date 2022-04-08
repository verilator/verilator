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
   // The '$c("1") &' ensures that dependent_clk does not get
   // replaced with clk early and hence hiding the issue
   wire  dependent_clk = $c1("1") & clk;

   int   n = 0;

   always @(posedge dependent_clk) begin
      $display("t=%t n=%d", $time, n);
      if ($time != (2*n+1) * 500) $stop;
      if (n == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      n += 1;
   end

endmodule
