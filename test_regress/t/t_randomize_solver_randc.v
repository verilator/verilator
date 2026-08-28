// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Flat;
  randc bit [1:0] c;
  rand bit [1:0] x;
  constraint rel {c < x;}
endclass

module t;
  Flat f;
  int ok;
  int good;
  int fails;
  initial begin
    f = new;
    f.srandom(11);
    good = 0;
    fails = 0;
    for (int i = 0; i < 6; ++i) begin
      ok = f.randomize();
      if (ok == 0)++fails;
      else ++good;
    end
    $write("NPASS=%0d NFAIL=%0d\n", good, fails);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
