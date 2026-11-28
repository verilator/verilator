// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A rand index into a non-rand member array reached through the explicit
// queue accessor: elaboration drops the accessor's index, so the select is
// rejected rather than expanded against an unknown element.

class Holder;
  bit [7:0] used[4];
endclass

class C1;
  rand int id;
  Holder hs[$];
  constraint c { id inside {[0:3]}; hs.at(0).used[id] == 8'h33; }
endclass

module t;
  initial begin
    C1 obj1;
    obj1 = new;
    if (obj1.randomize() == 0) $stop;
    $finish;
  end
endmodule
