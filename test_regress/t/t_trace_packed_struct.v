// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Andrew Bardsley.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   int cnt;

   // This won't compile with tracing as an incorrect declaration is made for
   // the temp variables used to represent the elements of localparam v
   typedef struct packed {
      logic [2:0][31:0] a;
   } t;

   localparam t v[2:0] = '{
       '{'{32'h10000002, 32'h10000001, 32'h10000000}},
       '{'{32'h20000002, 32'h20000001, 32'h20000000}},
       '{'{32'h30000002, 32'h30000001, 32'h30000000}}
   };

   initial cnt = 0;
   always@(posedge clk) begin
      if (cnt < 3) begin
          cnt = cnt + 1;
      end
      else begin
          $write("*-* All Finished *-*\n");
          $finish;
      end
   end
endmodule
