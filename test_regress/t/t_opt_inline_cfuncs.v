// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test module designed to generate multiple small CFuncs that can be inlined
module t;
   // Use initial block to avoid combinational loop issues
   reg [31:0] a, b, c, d;
   reg [7:0] local_x, local_y;

   initial begin
      // Initialize values
      a = 32'd10;
      b = 32'd20;

      // Local variable usage (tests variable merging)
      local_x = a[7:0];
      local_y = local_x + 8'd5;
      c = {24'b0, local_y};

      // Simple arithmetic
      d = a + b + c;

      // Verify results
      if (d == 32'd45) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("%%Error: d=%0d, expected 45\n", d);
         $stop;
      end
   end
endmodule
