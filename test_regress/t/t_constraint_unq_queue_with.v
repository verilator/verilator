// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Francesco Urbani
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A class with no class-level constraint block at all: the queue's size and
// its whole-array unique{} constraint are both written inline in the
// randomize() with {} call. Exercises the queue (rather than dynamic array)
// element-table refresh path, and the case where there is no class-level
// generator to fall back on.
class Foo;
  rand logic[2:0] q[$];
endclass

module t;
  initial begin
    automatic Foo f = new;
    automatic int ok;
    repeat (20) begin
      ok = f.randomize() with {q.size() == 4; unique {q};};
      `checkd(ok, 1)
      `checkd(f.q.size(), 4)
      for (int i = 0; i < 4; i++) begin
        for (int j = i + 1; j < 4; j++) begin
          if (f.q[i] == f.q[j]) begin
            $write("%%Error: q[%0d] == q[%0d] == %0d, not unique\n", i, j, f.q[i]);
            `stop;
          end
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
