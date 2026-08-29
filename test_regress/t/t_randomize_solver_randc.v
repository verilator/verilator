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

class Phased;
  randc bit [1:0] c;
  rand bit [1:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > {2'b00, x};}
  constraint link_c {c < x;}
endclass

module t;
  Flat f;
  Phased p;
  int ok;
  int good;
  int fails;
  initial begin
    good = 0;
    fails = 0;
    if ($test$plusargs("PHASED")) begin
      p = new;
      p.srandom(60);
      for (int i = 0; i < 12; ++i) begin
        ok = p.randomize();
        if (ok == 0)++fails;
        else ++good;
      end
    end
    else begin
      f = new;
      f.srandom(11);
      for (int i = 0; i < 6; ++i) begin
        ok = f.randomize();
        if (ok == 0)++fails;
        else ++good;
      end
    end
    $write("NPASS=%0d NFAIL=%0d\n", good, fails);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
