// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Verilator Authors.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef struct {
  rand bit values[];
} Element;

class Container;
  rand Element elements[];
endclass

module t;
  initial begin
    automatic Container object = new;
    void'(object.randomize());

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
