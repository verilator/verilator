// DESCRIPTION: Verilator: Verilog Test module for Issue#1631
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Julien Margetts.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   clk
   );
   input clk;

   localparam N = 4;

   wire [7:0] cval1[0:N-1];
   wire [7:0] cval2[N-1:0];
   wire [7:0] cval3[0:N-1];
   wire [7:0] cval4[N-1:0];

   wire [3:0] inc;

   assign inc = 4'b0001;

   // verilator lint_off LITENDIAN

   COUNTER UCOUNTER1[N-1:0]
     (
      .clk    (clk),
      .inc    (inc),
      .o      (cval1) // Twisted
      );

   COUNTER UCOUNTER2[N-1:0]
     (
      .clk    (clk),
      .inc    (inc),
      .o      (cval2) // Matches
      );

   COUNTER UCOUNTER3[0:N-1]
     (
      .clk    (clk),
      .inc    (inc),
      .o      (cval3) // Matches
      );

   COUNTER UCOUNTER4[0:N-1]
     (
      .clk    (clk),
      .inc    (inc),
      .o      (cval4) // Twisted
      );

   always @(posedge clk) begin
      if ((cval1[3] != cval2[0]) || (cval3[3] != cval4[0]))
        $stop;

      if ((cval1[0] + cval1[1] + cval1[2] + cval2[1] + cval2[2] + cval2[3] +
           cval3[0] + cval3[1] + cval3[2] + cval4[1] + cval4[2] + cval4[3]) != 0)
        $stop;

`ifdef TEST_VERBOSE
      $display("%d %d %d %d", cval1[0], cval1[1], cval1[2], cval1[3]);
      $display("%d %d %d %d", cval2[0], cval2[1], cval2[2], cval2[3]);
      $display("%d %d %d %d", cval3[0], cval3[1], cval3[2], cval3[3]);
      $display("%d %d %d %d", cval4[0], cval4[1], cval4[2], cval4[3]);
`endif

      if (cval1[0] + cval1[3] > 3) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module COUNTER
  (
   input            clk,
   input            inc,
   output reg [7:0] o
   );

   initial o = 8'd0;  // No reset input

   always @(posedge clk) if (inc) o <= o + 1;

endmodule
