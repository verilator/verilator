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
//
// The size constraint is a range (not a single fixed value), so repeated
// calls can settle on different sizes; the test checks that at least two
// different sizes are actually observed, confirming randomize() isn't stuck
// always returning the same solution.
class Foo;
  rand logic [2:0] q[$];
endclass

module t;
  initial begin
    automatic Foo f = new;
    automatic int ok;
    automatic int sz;
    automatic int first_size = -1;
    automatic bit found_variety = 0;
    repeat (30) begin
      ok = f.randomize() with {
        q.size() inside {[3 : 5]};
        unique {q};
      };
      `checkd(ok, 1)
      sz = f.q.size();
      if (sz < 3 || sz > 5) begin
        $write("%%Error: q.size()=%0d not in [3:5]\n", sz);
        `stop;
      end
      if (first_size == -1) first_size = sz;
      else if (sz != first_size) found_variety = 1;
      for (int i = 0; i < sz; i++) begin
        for (int j = i + 1; j < sz; j++) begin
          if (f.q[i] == f.q[j]) begin
            $write("%%Error: q[%0d] == q[%0d] == %0d, not unique\n", i, j, f.q[i]);
            `stop;
          end
        end
      end
    end
    if (!found_variety) begin
      $write("%%Error: randomize() always produced q.size()=%0d, no variety across repeats\n",
             first_size);
      `stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
