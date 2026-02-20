// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Driss Hafdi
// SPDX-License-Identifier: CC0-1.0

module t;

   // bug1624
   test #(.PARAM(32'd0)) test_i();

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module test
  #(
    parameter logic PARAM = 1'b0
    ) ();
endmodule
