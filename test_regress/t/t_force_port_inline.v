// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module sub(
   input wire [7:0] i,
   output wire [7:0] o
);
   // Must inline this module
   // verilator inline_module

   wire [7:0] m;
   assign m = i;
   assign o = m;
endmodule

module top;
   // Variable input
   reg [7:0] i = 8'h01;
   reg [7:0] o_v;
   sub sub_v(i, o_v);

   // Constant input
   reg [7:0] o_c;
   sub sub_c(8'h10, o_c);

   logic clk = 1'b0;
   always #1 clk = ~clk;
   int cyc = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         `checkh(i,       8'h01);
         `checkh(sub_v.i, 8'h01);
         `checkh(sub_v.m, 8'h01);
         `checkh(sub_v.o, 8'h01);
         `checkh(o_v,     8'h01);
         `checkh(sub_c.i, 8'h10);
         `checkh(sub_c.m, 8'h10);
         `checkh(sub_c.o, 8'h10);
         `checkh(o_c,     8'h10);
      end
      else if (cyc == 2) begin
         force sub_v.i = 8'h02;
         force sub_v.m = 8'h03;
         force sub_v.o = 8'h04;
         force sub_c.i = 8'h20;
         force sub_c.m = 8'h30;
         force sub_c.o = 8'h40;
      end
      else if (cyc == 3) begin
         `checkh(i,       8'h01);
         `checkh(sub_v.i, 8'h02);
         `checkh(sub_v.m, 8'h03);
         `checkh(sub_v.o, 8'h04);
         `checkh(o_v,     8'h04);
         `checkh(sub_c.i, 8'h20);
         `checkh(sub_c.m, 8'h30);
         `checkh(sub_c.o, 8'h40);
         `checkh(o_c,     8'h40);
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
