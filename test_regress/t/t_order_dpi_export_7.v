// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2022 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module testbench;

   logic clk;
   logic data;

   export "DPI-C" function set_inputs;
   function void set_inputs(bit val);
      clk = val;
      data = val;
   endfunction;

   // This needs to be in the 'ico' region. Written with $c1 to prevent
   // gate optimization.
   wire invdata = $c1(1) ^ data;

   int   n = 0;

   always @(edge clk) begin
      // The combinational update needs to have take effect (in the 'ico'
      // region), before this always block is executed
      if (invdata != ~data) $stop;
      $display("t=%t n=%d", $time, n);
      if ($time != (1*n+1) * 500) $stop;
      if (n == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      n += 1;
   end

endmodule
