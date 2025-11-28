// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

parameter INSTANCES = 20;

module t (clk);
   input clk;

   generate
      for (genvar i = 0; i < INSTANCES; ++i) sub sub (.*);
   endgenerate

   always @(posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub(input clk);
   logic simple_not;
   assign simple_not = ~clk;

   logic [7:0] counter;
   logic [7:0] add_result;
   logic [7:0] mul_result;
   assign add_result = counter + 8'd5;
   assign mul_result = add_result * 8'd3;

   logic [15:0] complex_a, complex_b;
   logic [31:0] complex_result;
   assign complex_result = {16'd0, {add_result, mul_result}} ^
                          ({{16'd0}, {complex_a[7:0], complex_a[15:8]}} +
                           {{16'd0}, {complex_b[7:0], complex_b[15:8]}});

   logic [15:0] conditional_result;
   assign conditional_result = (counter > 8'd100) ?
                               ({add_result, mul_result} & 16'hFF00) :
                               ({mul_result, add_result} | 16'h00FF);

   // Multi-level logic
   logic stage1, stage2, stage3;
   assign stage1 = (counter[0] ^ counter[1]) & clk;
   assign stage2 = (stage1 | counter[2]) ^ counter[3];
   assign stage3 = stage2 & (counter[4] | ~counter[5]);

   always @(posedge clk) begin
      counter <= counter + 1;
      complex_a <= complex_a + 16'd7;
      complex_b <= complex_b + 16'd13;
   end
endmodule
