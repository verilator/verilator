// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk, Rand);
   input clk;
   output reg [31:0] Rand;

`ifdef verilator
   `systemc_interface
     unsigned int QxRandTbl (unsigned int tbl, unsigned int idx) { return 0xfeed0fad; }
   `verilog
`endif

   function [31:0] QxRand32;
      /* verilator public */
      input [7:0]    tbl;
      input [7:0]    idx;
      begin
`ifdef verilator
	 QxRand32 = $c ("QxRandTbl(",tbl,",",idx,")");
`else
	 QxRand32 = 32'hfeed0fad;
`endif
      end
   endfunction

   always @(posedge clk) begin
      Rand <= #1 QxRand32 (8'h0, 8'h7);
   end
endmodule
