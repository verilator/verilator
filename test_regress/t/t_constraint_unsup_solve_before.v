// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand bit [7:0] data[5];
   rand bit x;

  constraint c_data {
    foreach (data[i]) {
      solve x before data[i];
      data[i] inside {8'h10, 8'h20, 8'h30, 8'h40, 8'h50};
    }
  }

endclass

module t;
   Packet p;

   initial begin
      p = new;
      void'(p.randomize());
   end
endmodule
