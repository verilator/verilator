// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


module sub();
  int sub_leaf = 0;
endmodule

module top();
  generate
    for (genvar i = -2; i < 0; ++i) begin : gen_loop
      int loop_local;
    end
  endgenerate

  sub i_sub [0:-2] ();

  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
