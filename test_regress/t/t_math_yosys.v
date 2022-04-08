// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Claire Wolf.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]           y1;                     // From d1 of demo_001.v
   wire [7:0]           y2;                     // From d1 of demo_001.v
   wire [7:0]           y3;                     // From d1 of demo_001.v
   wire [7:0]           y4;                     // From d1 of demo_001.v
   wire [31:0]          z0;                     // From d2 of demo_002.v
   wire [31:0]          z1;                     // From d2 of demo_002.v
   wire [31:0]          z2;                     // From d2 of demo_002.v
   wire [31:0]          z3;                     // From d2 of demo_002.v
   // End of automatics

   demo_001 d1(/*AUTOINST*/
               // Outputs
               .y1                      (y1[7:0]),
               .y2                      (y2[7:0]),
               .y3                      (y3[7:0]),
               .y4                      (y4[7:0]));
   demo_002 d2(/*AUTOINST*/
               // Outputs
               .z0                      (z0[31:0]),
               .z1                      (z1[31:0]),
               .z2                      (z2[31:0]),
               .z3                      (z3[31:0]));

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (y1 !== 8'h7b) $stop;
      if (y2 !== 8'h7c) $stop;
      if (y3 !== 8'h7b) $stop;
      if (y4 !== 8'h7c) $stop;
      if (z0 !== 32'h00000000) $stop;
      if (z1 !== 32'hffffffff) $stop;
      if (z2 !== 32'hffffffff) $stop;
      if (z3 !== 32'hffffffff) $stop;
      if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module demo_001(y1, y2, y3, y4);
   output [7:0] y1, y2, y3, y4;

   // verilator lint_off REALCVT
   localparam [7:0] p1 = 123.45;
   localparam real p2 = 123.45;
   localparam real p3 = 123;
   localparam p4 = 123.45;

   // verilator lint_off WIDTH
   assign y1 = p1 + 0.2;
   assign y2 = p2 + 0.2;
   assign y3 = p3 + 0.2;
   assign y4 = p4 + 0.2;
   // verilator lint_on WIDTH
endmodule

module demo_002(z0, z1, z2, z3);
   output [31:0] z0, z1, z2, z3;

   // verilator lint_off WIDTH
   assign z0 = 1'bx >= (-1 * -1.17);
   // verilator lint_on WIDTH
   assign z1 = 1 ?  1 ?  -1 : 'd0 : 0.0;
   assign z2 = 1 ? -1 :   1 ? 'd0 : 0.0;
   assign z3 = 1 ? -1 : 'd0;
endmodule
