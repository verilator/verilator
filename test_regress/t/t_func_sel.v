// DESCRIPTION: Verilator: Verilog Test module
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   parameter W = 104;

   integer cyc = 0;
   reg [63:0] crc;
   reg [127:0] sum;
   wire [127:0] result;

   wire [103:0] in;
   reg [103:0]  out;

   assign in = {crc[39:0], crc[63:0]};

   always @(posedge clk) begin
      out <= reverse(in);
   end

   assign result = {24'h0, out };

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x in=%x out=%x\n",
             $time, cyc, crc, result, in, out);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= {sum[127:1], 1'b0} + result;

      if (cyc < 10) begin
         crc <= 1;
         sum <= '0;
      end
      else if (cyc >= 90) begin
         $display("SUM = %x_%x_%x_%x", sum[127:96],
                  sum[95:64], sum[63:32], sum[31:0]);
`define EXPECTED_SUM 128'h00002d36_42d1a346_8d1a5936_42d1a319
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   function [W-1:0] reverse(input [W-1:0] val);
      integer i;
      // Bug workaround: reverse = '0;
      for (i = 0; i < W; i = i + 1)
        reverse[W-1-i] = val[i];
   endfunction
endmodule
