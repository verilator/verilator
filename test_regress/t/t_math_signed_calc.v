// DESCRIPTION: Verilator: Verilog Test module
//
// This mode performs signed number computations in the case of a particular
// interface definition.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Raynard Qiao.
// SPDX-License-Identifier: CC0-1.0

// issure 3294
module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [7:0] in0;
   reg [7:0] in1;
   reg [15:0] out;
   initial begin
      in0 = 'h2;
      in1 = 'hff;
   end
   Test test(.in0, .in1, .out);

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $display("[%0t] clk @ out 'h%0x, expect value='hfffe", $time, out);
`endif
      if (out !== 'hfffe) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule


module Test(in0, in1, out);
  input [7:0] in0;
  input [7:0] in1;
  output  [15:0] out;
  wire signed [7:0] in1;
  wire signed [7:0] in0;
  wire signed [15:0] out;

  assign out = $signed({1'b0, in0}) * in1;      // this operator should be  signed multiplication
endmodule
