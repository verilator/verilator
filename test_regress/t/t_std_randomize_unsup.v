// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef struct {int f;} S;

class Item;
  int x;
endclass

module t;
  initial begin
    int q[$];
    S sq[$];
    Item hq[$];
    int ok;
    ok = std::randomize(q[0]);
    ok = std::randomize(q[$]);
    ok = std::randomize(sq[0].f);
    ok = std::randomize(hq[0].x);
    $finish;
  end
endmodule
