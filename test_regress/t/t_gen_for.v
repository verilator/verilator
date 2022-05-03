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
   integer      cyc = 0;

   reg [7:0] crc;
   genvar g;

   wire [7:0]   out_p1;
   wire [15:0]  out_p2;
   wire [7:0]   out_p3;
   wire [7:0]   out_p4;

   paramed #(.WIDTH(8),  .MODE(0)) p1 (.in(crc), .out(out_p1));
   paramed #(.WIDTH(16), .MODE(1)) p2 (.in({crc,crc}), .out(out_p2));
   paramed #(.WIDTH(8),  .MODE(2)) p3 (.in(crc), .out(out_p3));
   gencase #(.MODE(3))             p4 (.in(crc), .out(out_p4));

   wire [7:0]   out_ef;
   enflop  #(.WIDTH(8))            enf (.a(crc), .q(out_ef), .oe_e1(1'b1), .clk(clk));

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d crc=%b %x %x %x %x %x\n", $time, cyc, crc, out_p1, out_p2, out_p3, out_p4, out_ef);
      cyc <= cyc + 1;
      crc <= {crc[6:0], ~^ {crc[7],crc[5],crc[4],crc[3]}};
      if (cyc==0) begin
         // Setup
         crc <= 8'hed;
      end
      else if (cyc==1) begin
      end
      else if (cyc==3) begin
         if (out_p1 !== 8'h2d) $stop;
         if (out_p2 !== 16'h2d2d) $stop;
         if (out_p3 !== 8'h78) $stop;
         if (out_p4 !== 8'h44) $stop;
         if (out_ef !== 8'hda) $stop;
      end
      else if (cyc==9) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module gencase (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   in
   );
   parameter MODE = 0;
   input [7:0] in;
   output [7:0] out;
   generate // : genblk1
      begin
         case (MODE)
           2:       mbuf mc [7:0] (.q(out[7:0]), .a({in[5:0],in[7:6]}));
           default: mbuf mc [7:0] (.q(out[7:0]), .a({in[3:0],in[3:0]}));
         endcase
      end
   endgenerate

endmodule

module paramed (/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   in
   );
   parameter WIDTH = 1;
   parameter MODE = 0;
   input [WIDTH-1:0] in;
   output [WIDTH-1:0] out;

   generate
      if (MODE==0) initial $write("Mode=0\n");
      // No else
   endgenerate

`ifndef NC  // for(genvar) unsupported
 `ifndef ATSIM  // for(genvar) unsupported
   generate
      // Empty loop body, local genvar
      for (genvar j=0; j<3; j=j+1) begin end
      // Ditto to make sure j has new scope
      for (genvar j=0; j<5; j=j+1) begin end
   endgenerate
 `endif
`endif

   generate
   endgenerate

   genvar             i;
   generate
      if (MODE==0) begin
         // Flip bitorder, direct assign method
         for (i=0; i<WIDTH; i=i+1) begin
            assign out[i] = in[WIDTH-i-1];
         end
      end
      else if (MODE==1) begin
         // Flip using instantiation
         for (i=0; i<WIDTH; i=i+1) begin
            integer from = WIDTH-i-1;
            if (i==0) begin     // Test if's within a for
               mbuf m0 (.q(out[i]), .a(in[from]));
            end
            else begin
               mbuf ma (.q(out[i]), .a(in[from]));
            end
         end
      end
      else begin
         for (i=0; i<WIDTH; i=i+1) begin
            mbuf ma (.q(out[i]), .a(in[i^1]));
         end
      end
   endgenerate

endmodule

module mbuf (
           input a,
           output q
           );
   assign         q = a;
endmodule

module enflop (clk, oe_e1, a,q);
   parameter WIDTH=1;

   input     clk;
   input     oe_e1;
   input  [WIDTH-1:0] a;
   output [WIDTH-1:0] q;

   reg [WIDTH-1:0]    oe_r;
   reg [WIDTH-1:0]    q_r;
   genvar             i;

   generate
      for (i = 0; i < WIDTH; i = i + 1) begin : datapath_bits
         enflop_one enflop_one
           (.clk        (clk),
            .d          (a[i]),
            .q_r        (q_r[i]));

         always @(posedge clk) oe_r[i] <= oe_e1;

         assign q[i] = oe_r[i] ? q_r[i] : 1'bx;
      end
   endgenerate
endmodule

module enflop_one (
                   input clk,
                   input d,
                   output reg q_r
                   );
   always @(posedge clk) q_r <= d;
endmodule
