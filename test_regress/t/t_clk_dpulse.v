// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // verilator lint_off GENCLK

   reg [7:0] cyc; initial cyc=0;
   reg 	     genclk;
   // verilator lint_off MULTIDRIVEN
   reg [7:0] set_both;
   // verilator lint_on MULTIDRIVEN

   wire genthiscyc = ( (cyc % 2) == 1 );

   always @ (posedge clk) begin
      cyc <= cyc + 8'h1;
      genclk <= genthiscyc;
      set_both <= cyc;
      $write ("SB set_both %x <= cyc %x\n", set_both, cyc);
      if (genthiscyc) begin
	 if (cyc>1 && set_both != (cyc - 8'h1)) $stop;
      end
      else begin
	 if (cyc>1 && set_both != ~(cyc - 8'h1)) $stop;
      end
      if (cyc==10) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

   always @ (posedge genclk) begin
      set_both <= ~ set_both;
      $write ("SB set_both %x <= cyc %x\n", set_both, ~cyc);
      if (cyc>1 && set_both != (cyc - 8'h1)) $stop;
   end

endmodule
