// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


module sub();
  int some_var = 0;
endmodule

module top();
  sub sub_a ();   // tagged public_flat
  sub sub_b ();   // tagged public_flat (same marking as sub_a -> shares clone)
  sub sub_c ();   // tagged public_flat_rd (different marking -> own clone)
  sub sub_d ();   // not tagged

  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
