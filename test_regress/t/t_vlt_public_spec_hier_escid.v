// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


module sub_mod();
  int \var.with.dot = 0;
endmodule

module top();
  sub_mod \inst.with.dot ();
  sub_mod \foo[abc] ();

  initial begin
    $c("Verilated::scopesDump();");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
