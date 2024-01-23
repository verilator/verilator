// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg  a1;
   wire a2 = ~a1;
   wire o1, o2;
   udp (o1, a1);
   udp (o2, a2);

   integer cyc;  initial cyc = 0;

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      a1  <= cyc[0];
      if (cyc==0) begin
      end
      else if (cyc<90) begin
         if (o1 !=  cyc[0]) $stop;
         if (o2 != !cyc[0]) $stop;
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

primitive udp(o,a);
   output o;
   input  a;
`ifdef verilator
   wire   o = ~a;
`else
   table
      //o a
      0 :  1;
      1 :  0;
   endtable
`endif
endprimitive
