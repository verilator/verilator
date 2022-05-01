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

   reg [41:0]           aaa;
   wire [41:0]          bbb;

   // verilator public_module
   wire [41:0]          z_0;
   wire [41:0]          z_1;

   wide w_0(
            .xxx( { {40{1'b0}},2'b11 } ),
            .yyy( aaa[1:0] ),
            .zzz( z_0 )
            );

   wide w_1(
            .xxx( aaa ),
            .yyy( 2'b10 ),
            .zzz( z_1 )
            );

   assign bbb= z_0 + z_1;

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            aaa <= 42'b01;
         end
         if (cyc==2) begin
            aaa <= 42'b10;
            if (z_0 != 42'h4) $stop;
            if (z_1 != 42'h3) $stop;
         end
         if (cyc==3) begin
            if (z_0 != 42'h5) $stop;
            if (z_1 != 42'h4) $stop;
         end
         if (cyc==4) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module wide (
        input [41:0]            xxx,
        input [1:0]                     yyy,
        output [41:0]           zzz
        );
   // verilator public_module

   assign zzz = xxx+ { {40{1'b0}},yyy };

endmodule
