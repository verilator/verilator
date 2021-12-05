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

   // verilator lint_off COMBDLY
   // verilator lint_off LATCH
   // verilator lint_off UNOPT
   // verilator lint_off UNOPTFLAT
   // verilator lint_off BLKANDNBLK

   reg         c1_start; initial c1_start = 0;
   wire [31:0] c1_count;
   comb_loop c1 (.count(c1_count), .start(c1_start));

   wire        s2_start = c1_start;
   wire [31:0] s2_count;
   seq_loop  s2 (.count(s2_count), .start(s2_start));

   wire        c3_start = (s2_count[0]);
   wire [31:0] c3_count;
   comb_loop c3 (.count(c3_count), .start(c3_start));

   reg [7:0] cyc; initial cyc = 0;
   always @ (posedge clk) begin
      //$write("[%0t] %x  counts %x %x %x\n", $time,cyc,c1_count,s2_count,c3_count);
      cyc <= cyc + 8'd1;
      case (cyc)
        8'd00: begin
           c1_start <= 1'b0;
        end
        8'd01: begin
           c1_start <= 1'b1;
        end
        default: ;
      endcase
      case (cyc)
        8'd02: begin
           // On Verilator, we expect these comparisons to match exactly,
           // confirming that our settle loop repeated the exact number of
           // iterations we expect. No '$stop' should be called here, and we
           // should reach the normal '$finish' below on the next cycle.
           if (c1_count!=32'h3) $stop;
           if (s2_count!=32'h3) $stop;
           if (c3_count!=32'h5) $stop;
        end
        8'd03: begin
           $write("*-* All Finished *-*\n");
           $finish;
        end
        default: ;
      endcase
   end
endmodule

module comb_loop (/*AUTOARG*/
   // Outputs
   count,
   // Inputs
   start
   );
   input start;
   output reg [31:0] count; initial count = 0;

   reg [31:0]    runnerm1, runner; initial runner = 0;

   always @ (posedge start) begin
      runner = 3;
   end

   always @ (/*AS*/runner) begin
      runnerm1 = runner - 32'd1;
   end

   always @ (/*AS*/runnerm1) begin
      if (runner > 0) begin
         count = count + 1;
         runner = runnerm1;
         $write ("%m count=%d  runner =%x\n",count, runnerm1);
      end
   end

endmodule

module seq_loop (/*AUTOARG*/
   // Outputs
   count,
   // Inputs
   start
   );
   input start;
   output reg [31:0] count; initial count = 0;

   reg [31:0]    runnerm1, runner; initial runner = 0;

   always @ (posedge start) begin
      runner <= 3;
   end

   always @ (/*AS*/runner) begin
      runnerm1 = runner - 32'd1;
   end

   always @ (/*AS*/runnerm1) begin
      if (runner > 0) begin
         count = count + 1;
         runner <= runnerm1;
         $write ("%m count=%d  runner<=%x\n",count, runnerm1);
      end
   end

endmodule
