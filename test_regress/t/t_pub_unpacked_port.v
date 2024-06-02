// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module sub (
   output logic [31:0] sub_s1up_out[0:0] /* verilator public_flat_rw */,
   input logic sub_clk,
   input logic [31:0] sub_s1up_in[0:0] /* verilator public_flat_rw */
   );

   // Evaluate clock edges
   always @(posedge sub_clk) begin
      sub_s1up_out <= sub_s1up_in;
   end

endmodule


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   logic   [31:0]     s1up_in[1];
   logic   [31:0]     s1up_out[1];

   sub the_sub (
      .sub_s1up_in (s1up_in),
      .sub_s1up_out (s1up_out),
      .sub_clk (clk));

   always_comb   s1up_in[0] = cyc;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      if (cyc == 10) begin
         if (s1up_out[0] != 9) begin
             $display("%%Error: got %0d instead of 9", s1up_out);
             $stop;
         end
         if (the_sub.sub_s1up_in[0] != 10) begin
             $display("%%Error: the_sub.sub_s1up_in was %0d instead of 10", the_sub.sub_s1up_in[0]);
             $stop;
         end
         $display("final cycle = %0d", cyc);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
