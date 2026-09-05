// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 18.4 type-eligibility rules for rand/randc. Each
// member below is illegal for a different reason.

class Item;
  rand int val;
endclass

interface Bus;
endinterface

typedef chandle chandle_q_t[$];

typedef union {
  int a;
  bit [31:0] b;
} unpacked_union_t;

class C;
  // Unpacked unions shall not be declared as rand or randc.
  randc unpacked_union_t union_randc;
  // Object handles shall not be declared randc.
  randc Item handle_randc;
  // Real (and shortreal, which promotes to real) shall not be randc.
  randc real real_randc;
  randc shortreal shortreal_randc;
  randc realtime realtime_randc;
  // Not in the rand type domain at all.
  rand chandle chandle_rand;
  rand string string_rand;
  rand event event_rand;
  // Not a basic type, checked separately.
  rand virtual Bus vif_rand;
  // Typedef'd queue: confirms the check unwraps both layers.
  rand chandle_q_t chandle_queue_rand;
endclass

module t;
  initial begin
    C obj;
    obj = new;
    if (obj.randomize() == 0) $stop;
  end
endmodule
