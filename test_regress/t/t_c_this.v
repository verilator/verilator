// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;
   always @(posedge clk) begin
     $cpure("const CData xthis = this->clk;");
     $cpure("const CData thisx = xthis;");
     $cpure("const CData xthisx = thisx;");
     $c("this->clk = xthisx;");
   end
endmodule
