// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// See bug5821

`define STRINGIFY(x) `"x`"

module imply(input logic p, input logic q, output logic r);
   always_comb begin
      r = p | q;
   end
endmodule

module t();
   logic p;
   logic q;
   logic r;

   imply dut(.p(p), .q(q), .r(r));

   initial begin
      $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
      $dumpvars();
      //
      p = 1;
      q = 0;
      $strobe("[%0t] %d, %d, %d", $time, p, q, r);
      #1;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
