// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   supply0 [1:0] low;
   supply1 [1:0] high;

   reg [7:0] isizedwire;
   reg ionewire;

   wire oonewire;
   wire [7:0]           osizedreg;              // From sub of t_inst_v2k_sub.v

   t_inst sub
     (
      .osizedreg,
      .oonewire,
      // Inputs
      .isizedwire                       (isizedwire[7:0]),
      .*
      //.ionewire                       (ionewire)
      );

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            ionewire <= 1'b1;
            isizedwire <= 8'd8;
         end
         if (cyc==2) begin
            if (low != 2'b00) $stop;
            if (high != 2'b11) $stop;
            if (oonewire !== 1'b1) $stop;
            if (isizedwire !== 8'd8) $stop;
         end
         if (cyc==3) begin
            ionewire <= 1'b0;
            isizedwire <= 8'd7;
         end
         if (cyc==4) begin
            if (oonewire !== 1'b0) $stop;
            if (isizedwire !== 8'd7) $stop;
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end
endmodule

module t_inst
  (
   output reg [7:0] osizedreg,
   output wire oonewire /*verilator public*/,
   input [7:0] isizedwire,
   input wire ionewire
   );

   assign oonewire = ionewire;

   always @* begin
      osizedreg = isizedwire;
   end

endmodule
