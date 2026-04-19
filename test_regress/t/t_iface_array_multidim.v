// DESCRIPTION: Verilator: multi-dimensional interface instance arrays.
//
// Minimal 2D reproducer -- exercises declaration, dotted access,
// multi-dim port connection and VCD-relevant naming.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface simple_if;
   logic [7:0] data;
endinterface

module t;
   localparam int A = 2;
   localparam int B = 3;

   simple_if bus [A-1:0][B-1:0] ();

   genvar gi, gj;
   generate
      for (gi = 0; gi < A; gi++) begin : g_a
         for (gj = 0; gj < B; gj++) begin : g_b
            initial bus[gi][gj].data = 8'(gi * B + gj + 1);
         end
      end
   endgenerate

   // Runtime check via a chk array populated by the same genvar generate block.
   logic [7:0] chk [A-1:0][B-1:0];
   generate
      for (gi = 0; gi < A; gi++) begin : g_a_chk
         for (gj = 0; gj < B; gj++) begin : g_b_chk
            always_comb chk[gi][gj] = bus[gi][gj].data;
         end
      end
   endgenerate

   initial begin
      #1;
      for (int i = 0; i < A; i++) begin
         for (int j = 0; j < B; j++) begin
            if (chk[i][j] !== 8'(i * B + j + 1)) begin
               $write("%%Error: bus[%0d][%0d].data=%0d expected %0d\n",
                      i, j, chk[i][j], i * B + j + 1);
               $stop;
            end
         end
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
