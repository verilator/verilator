// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;
   always @(posedge clk) begin
     $c("const CData xthis = this->clk;");
     $c("const CData thisx = xthis;");
     $c("const CData xthisx = thisx;");
     $c("this->clk = xthisx;");
   end
endmodule
