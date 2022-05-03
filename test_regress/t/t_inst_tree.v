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
   integer cyc; initial cyc=1;

   // verilator lint_off GENCLK
   reg     printclk;
   // verilator lint_on GENCLK
   ps ps (printclk);

   reg [7:0] a;
   wire [7:0] z;

   l1 u (~a,z);

   always @ (posedge clk) begin
      printclk <= 0;
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            printclk <= 1'b1;
         end
         if (cyc==2) begin
            a <= 8'b1;
         end
         if (cyc==3) begin
            if (z !== 8'hf8) $stop;
            //if (u.u1.u1.u1.u0.PARAM !== 1) $stop;
            //if (u.u1.u1.u1.u1.PARAM !== 2) $stop;
            //if (u.u0.u0.u0.u0.z !== 8'hfe) $stop;
            //if (u.u0.u0.u0.u1.z !== 8'hff) $stop;
            //if (u.u1.u1.u1.u0.z !== 8'h00) $stop;
            //if (u.u1.u1.u1.u1.z !== 8'h01) $stop;
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module ps (input printclk);
   // Check that %m stays correct across inlines
   always @ (posedge printclk) $write("[%0t] %m: Clocked\n", $time);
endmodule

module l1 (input [7:0] a, output [7:0] z);
   wire [7:0] z0; wire [7:0] z1;
   assign z = z0+z1;
   l2 u0 (a, z0);   l2 u1 (a, z1);
endmodule

module l2 (input [7:0] a, output [7:0] z);
   wire [7:0] z0; wire [7:0] z1;
   assign z = z0+z1;
   wire [7:0] a1 = a+8'd1;
   l3 u0 (a, z0);   l3 u1 (a1, z1);
endmodule

module l3 (input [7:0] a, output [7:0] z);
   wire [7:0] z0; wire [7:0] z1;
   assign z = z0+z1;
   wire [7:0] a1 = a+8'd1;
   l4 u0 (a, z0);   l4 u1 (a1, z1);
endmodule

module l4 (input [7:0] a, output [7:0] z);
   wire [7:0] z0; wire [7:0] z1;
   assign z = z0+z1;
   wire [7:0] a1 = a+8'd1;
   l5 #(1) u0 (a, z0);   l5 #(2) u1 (a1, z1);
endmodule

module l5 (input [7:0] a, output [7:0] z);
   parameter PARAM = 5;
   wire [7:0] z0; wire [7:0] z1;
   assign z = a;
endmodule
