// DESCRIPTION: Verilator: Verilog Test module
//
// Asserts that a struct whose leaves are tracked separately for force reports
// the read-write reference error, the same as a scalar does, when it is passed
// by reference somewhere its value would have to be read and written as a whole.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef struct {
    logic [7:0] arr[4];
    logic [7:0] sc;
  } st_t;

  class Cls;
    task take_ref(ref st_t r);
    endtask
  endclass

  st_t s;
  Cls cls = new;

  initial begin
    force s.arr[2] = 8'haa;
    cls.take_ref(s);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
