// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   logic [31:0] a;

   // verilator lint_off IMPLICIT
   assign (highz0, supply1) nt00 = a[0];
   assign (supply0, highz1) nt01 = a[0];
   assign (supply0, supply1) nt02 = a[0];
   assign (strong0, strong1) nt03 = a[0];
   assign (pull0, pull1) nt04 = a[0];
   assign (weak0, weak1) nt05 = a[0];

   assign (highz0, supply1) nt10 = a[0];
   assign (supply0, highz1) nt11 = a[0];
   assign (supply0, supply1) nt12 = a[0];
   assign (strong0, strong1) nt13 = a[0];
   assign (pull0, pull1) nt14 = a[0];
   assign (weak0, weak1) nt15 = a[0];
   // verilator lint_on IMPLICIT

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            a <= 32'h18f6b030;
         end
         if (cyc==2) begin
            a <= 32'h18f6b03f;
            if (nt00 !== 1'b0) $stop;
            if (nt01 !== 1'b0) $stop;
            if (nt02 !== 1'b0) $stop;
            if (nt03 !== 1'b0) $stop;
            if (nt04 !== 1'b0) $stop;
            if (nt05 !== 1'b0) $stop;
            if (nt10 !== 1'b0) $stop;
            if (nt11 !== 1'b0) $stop;
            if (nt12 !== 1'b0) $stop;
            if (nt13 !== 1'b0) $stop;
            if (nt14 !== 1'b0) $stop;
            if (nt15 !== 1'b0) $stop;
         end
         if (cyc==3) begin
            if (nt00 !== 1'b1) $stop;
            if (nt01 !== 1'b1) $stop;
            if (nt02 !== 1'b1) $stop;
            if (nt03 !== 1'b1) $stop;
            if (nt04 !== 1'b1) $stop;
            if (nt05 !== 1'b1) $stop;
            if (nt10 !== 1'b1) $stop;
            if (nt11 !== 1'b1) $stop;
            if (nt12 !== 1'b1) $stop;
            if (nt13 !== 1'b1) $stop;
            if (nt14 !== 1'b1) $stop;
            if (nt15 !== 1'b1) $stop;
         end
         if (cyc==4) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
