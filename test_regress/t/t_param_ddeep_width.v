// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use.
// SPDX-License-Identifier: CC0-1.0

// bug541
module t(clk,odata);
   input clk;
   output [7:0] odata;
   paramtest_DFFRE #(1) dffre0(clk,odata[7]);
   paramtest_WRAP #(7) dffe0(clk,odata[6:0]);
endmodule

module paramtest_WRAP(clk,q);
   parameter W=1;
   input clk;
   output [W-1:0] q;
   paramtest_DFFRE #(W) dffre0(clk,q);
endmodule

module paramtest_DFFRE(clk,q);
   parameter W=1;
   parameter [W-1:0] INIT={W{1'b0}};
   input clk;
   output [W-1:0] q;
   reg [W-1:0]    q;
   always @(posedge clk) begin
      q <= INIT;
   end
endmodule
