// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

typedef struct {
  rand bit l;
  rand bit x;
  rand bit w;
  rand bit r;
} reg_t;

class Packet;
   rand bit [7:0] data[5];
   rand bit x;

  constraint c_data {
    foreach (data[i]) {
      solve x before data[i];
      data[i] inside {8'h10, 8'h20, 8'h30, 8'h40, 8'h50};
    }
  }

  rand reg_t cfg[];

  constraint solves_only_c {
    foreach (cfg[i]) {
      solve x before cfg[i].w, cfg[i].r;
      solve cfg[i].l before cfg[i].x;
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
