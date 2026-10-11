// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Saqib Khan
// SPDX-License-Identifier: CC0-1.0

// Enum item through a parameterized instance in randomize-with (#8347) (#8389)

class Item;
  rand int x;
endclass

module child #(
    parameter int W = 1
);
  typedef enum logic [1:0] {
    S_IDLE = 0,
    S_WORK = 2'(W)
  } state_t;
endmodule

module t;
  child #(.W(2)) a ();
  child #(.W(3)) b ();
  Item items[4];

  initial begin
    items[a.S_WORK] = new;
    items[b.S_WORK] = new;
    // Same enum item reference in randomize object and constraint
    void'(items[a.S_WORK].randomize() with {items[a.S_WORK].x == 5;});
    // Different enum item references
    void'(items[a.S_WORK].randomize() with {items[b.S_WORK].x == 5;});
  end
endmodule
