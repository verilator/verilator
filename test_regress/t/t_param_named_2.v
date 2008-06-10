// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   parameter PAR = 3;
   input clk;

   m3 m3_inst (.clk(clk));
   defparam m3_inst.FROMDEFP = 19;
   defparam m3_inst.P2 = 2;
   //defparam m3_inst.P3 = PAR;
   defparam m3_inst.P3 = 3;

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
    (/*AUTOARG*/
     // Inputs
     clk
     );
   input       clk;
   localparam  LOC = 13;

   parameter   UNCH = 99;
   parameter   P1 = 10;
   parameter   P2 = 20;
   parameter   P3 = 30;

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
