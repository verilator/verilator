// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   reg [2:0] a;
   reg [2:0] b;
   reg       q;

   f6 f6 (/*AUTOINST*/
          // Outputs
          .q                            (q),
          // Inputs
          .a                            (a[2:0]),
          .b                            (b[2:0]),
          .clk                          (clk));

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            a <= 3'b000;
            b <= 3'b100;
         end
         if (cyc==2) begin
            a <= 3'b011;
            b <= 3'b001;
            if (q != 1'b0) $stop;
         end
         if (cyc==3) begin
            a <= 3'b011;
            b <= 3'b011;
            if (q != 1'b0) $stop;
         end
         if (cyc==9) begin
            if (q != 1'b1) $stop;
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule

module f6 (a, b, clk, q);
   input  [2:0] a;
   input [2:0]  b;
   input        clk;
   output       q;
   reg          out;

   function func6;
      reg       result;
      input [5:0] src;
      begin
         if (src[5:0] == 6'b011011) begin
            result = 1'b1;
         end
         else begin
            result = 1'b0;
         end
         func6 = result;
      end
   endfunction

   wire [5:0] w6 = {a, b};
   always @(posedge clk) begin
      out <= func6(w6);
   end

   assign q = out;

endmodule
