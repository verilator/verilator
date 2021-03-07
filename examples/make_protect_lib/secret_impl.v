// DESCRIPTION: Verilator: --protect-lib example secret module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

// This module will be used as libsecret.a or libsecret.so without
// exposing the source.

module secret_impl
  (
   input [31:0]        a,
   input [31:0]        b,
   output logic [31:0] x,
   input               clk);

   logic [31:0]        accum_q = 0;
   logic [31:0]        secret_value = 9;

   initial $display("[%0t] %m: initialized", $time);

   always @(posedge clk) begin
      accum_q <= accum_q + a;
      if (accum_q > 10)
        x <= b;
      else
        x <= a + b + secret_value;
   end

endmodule
