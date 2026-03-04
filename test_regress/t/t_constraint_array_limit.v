// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test that array reduction constraints are ignored when array size exceeds --constraint-array-limit
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class Packet;
  rand int data[32];

  constraint c {
    data.sum() with (item) < 1000;
  }

  function void verify();
    int i;
    i = randomize();
    `checkd(i, 1);
  endfunction
endclass

module t;
  initial begin
    Packet p;
    int success_count;

    p = new;

    // Try randomization -- should fail with a warning
    p.verify();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
