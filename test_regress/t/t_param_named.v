// $Id:$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   parameter PAR = 3;
   input clk;

   defparam m3.FROMDEFP = 19;

   m3 #(.P3(PAR),
	.P2(2))
     m3(.clk(clk));

   integer cyc=1;
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==1) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module m3
`ifdef verilator
  #(
    parameter  UNCH = 99;
    parameter  P1 = 10;
    parameter  P2 = 20,
               P3 = 30;
    )
`endif
    (/*AUTOARG*/
     // Inputs
     clk
     );
   input       clk;
   localparam  LOC = 13;

`ifndef verilator   // Vcs not compliant yet
   parameter   UNCH = 99;
   parameter   P1 = 10;
   parameter   P2 = 20;
   parameter   P3 = 30;
`endif

   parameter   FROMDEFP = 11;

   initial begin
      $display("%x %x %x",P1,P2,P3);
   end
   always @ (posedge clk) begin
      if (UNCH !== 99) $stop;
      if (P1 !== 10) $stop;
      if (P2 !== 2) $stop;
      if (P3 !== 3) $stop;
      if (FROMDEFP !== 19) $stop;
   end
endmodule
