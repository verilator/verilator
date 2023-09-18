// DESCRIPTION: Verilator: Verilog Test module for issue #2938
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Julien Margetts (Originally provided by YanJiun)
// SPDX-License-Identifier: Unlicense

module test (
  input      [2:0] a,
  input      [3:0] c,

  output reg [7:0] o1,
  output reg [7:0] o2
);

   integer         i;

   always @ (*) begin
      case(a)
        {3'b000}: o1 = 8'd1;
        {3'b001}:
          for(i=0;i<4;i=i+1) o1[i*2+:2] = 2'(c[i]);
        {3'b010}: o1 = 8'd3;
        {3'b011}: o1 = 8'd4;
        default : o1 = 0;
      endcase
   end

   always_comb begin
      unique if (a[0]) o2 = 1;
      else if (a[1]) o2 = 2;
      else o2 = 3;
   end

endmodule
