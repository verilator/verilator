// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, reset_l
   );

   input        clk;
   input        reset_l;

   generate
      show #(`__LINE__, "top.t.show0") show0();

      if (0) ;
      else if (0) ;
      else if (1) show #(`__LINE__, "top.t.genblk1.show1") show1();

      if (0) begin end
      else if (0) begin end
      else if (1) begin show #(`__LINE__, "top.t.genblk2.show2") show2(); end

      if (0) ;
      else begin
         if (0) begin end
         else if (1) begin show #(`__LINE__, "top.t.genblk3.genblk1.show3") show3(); end
      end

      if (0) ;
      else begin : x1
         if (0) begin : x2 end
         else if (1) begin : x3 show #(`__LINE__, "top.t.x1.x3.show4") show4(); end
      end
   endgenerate

   int cyc;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end

   end
endmodule

module show #(parameter LINE=0, parameter string EXPT) ();
   always @ (posedge t.clk) begin
      if (t.cyc == LINE) begin
         $display("%03d: exp=%s got=%m", LINE, EXPT);
      end
   end
endmodule
