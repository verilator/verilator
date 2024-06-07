// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   vlan,
   // Inputs
   clk, pkt_data
   );

   parameter WIDTH = 320;
   input clk;
   input [2559:0] pkt_data;
   output reg [15:0] vlan;

   always @(posedge clk) begin
      // verilator lint_off WIDTHCONCAT
      // verilator lint_off WIDTHTRUNC
      vlan <= pkt_data[ { (WIDTH-12), 3'b0 } - 1 -: 16];
      // verilator lint_on WIDTHCONCAT
      // verilator lint_on WIDTHTRUNC
   end

endmodule
