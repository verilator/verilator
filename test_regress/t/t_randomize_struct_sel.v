// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef struct {int x;} struct_t;

class ConstrClass;
  struct_t obj;
  rand int rand_int;
  constraint addr_c {rand_int == obj.x;}
endclass

module t;
  ConstrClass o;
  initial begin
    o = new;
    o.obj.x = 42;
    if (o.randomize() == 0) begin
      $display("Randomization failed");
      $stop;
    end else if (o.obj.x != o.rand_int) $stop;
    $finish;
  end
endmodule
