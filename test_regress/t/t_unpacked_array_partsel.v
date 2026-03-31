// DESCRIPTION: Verilator: Test unpacked array with part-select assignment
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that assigning to part-selects of unpacked array elements works
// without spurious "Unsupported LHS tristate construct: ARRAYSEL" errors.
// This is a non-tristate design - the error was a false positive.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // Unpacked array of packed vectors
   wire [15:0] packed_in_unpacked [0:3];

   // Source data
   wire [7:0] source [0:3];
   assign source[0] = 8'hAA;
   assign source[1] = 8'hBB;
   assign source[2] = 8'hCC;
   assign source[3] = 8'hDD;

   // Assign to part-selects of unpacked array elements
   // This pattern was incorrectly flagged as tristate
   genvar i;
   generate
      for (i = 0; i < 4; i = i + 1) begin : gen_assign
         assign packed_in_unpacked[i][7:0] = source[i];
         assign packed_in_unpacked[i][15:8] = ~source[i];
      end
   endgenerate

   // Verification
   integer cyc = 0;
   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 5) begin
         if (packed_in_unpacked[0] !== 16'h55AA) $stop;
         if (packed_in_unpacked[1] !== 16'h44BB) $stop;
         if (packed_in_unpacked[2] !== 16'h33CC) $stop;
         if (packed_in_unpacked[3] !== 16'h22DD) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
