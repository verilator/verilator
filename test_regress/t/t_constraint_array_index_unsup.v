// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test that item.index in array reduction constraints is not yet supported
class Packet;
  rand bit [3:0] data[5];

  constraint c {
     // This should trigger unsupported warning
     data.sum() with (item.index) <= 10;
  }
endclass

module t;
  initial begin
     Packet p;
     int i;

     p = new;

     i = p.randomize();

     $write("*-* All Finished *-*\n");
     $finish;
  end
endmodule
