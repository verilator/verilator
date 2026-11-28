// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A queue access spelled with the explicit accessor instead of brackets:
// elaboration drops its index, so the comparison is rejected rather than
// expanded against an unknown row.

class C1;
  rand bit [7:0] frame[2];
  bit [7:0] target[$][2];
  constraint c { frame == target.at(0); }
  function new();
    target = '{'{0, 0}};
  endfunction
endclass

// Same, but the unsupported operand is on the left instead of the right.
class C2;
  rand bit [7:0] frame[2];
  bit [7:0] target[$][2];
  constraint c { target.at(0) == frame; }
  function new();
    target = '{'{0, 0}};
  endfunction
endclass

module t;
  initial begin
    C1 obj1;
    C2 obj2;
    obj1 = new;
    obj2 = new;
    if (obj1.randomize() == 0) $stop;
    if (obj2.randomize() == 0) $stop;
  end
endmodule
