// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // Values to swap and locations for the swapped values.
   reg [31:0] x = 32'ha5a5a5a5;
   wire [31:0] y;

   testit testi_i (.a (x[7:0]),
                   .b (y[31:24]));

   always @ (posedge clk) begin
      x <= {x[30:0],1'b0};
      $write("x = %x, y = %x\n", x, y);

      if (x[3:0] != 4'h0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule


// Swap the byte order of two args.
module testit (input  wire [7:0] a,
               output wire [7:0] b
               );

   alias b = {a[3:0],a[7:4]};

endmodule
