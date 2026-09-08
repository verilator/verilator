// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Francesco Urbani
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// No class-level constraint at all. A first randomize() with {} call sizes
// the array inline; a second, separate with{} call adds only a unique{} on
// the same (already-sized) array, with no size reference of its own. That
// second call's two-phase solve has nothing to resize.
//
// arr's element type has only 4 possible values (2'b00-2'b11), and the array
// is exactly 4 elements long, so unique{} leaves only one outcome per solve:
// arr must be some permutation of {0, 1, 2, 3}. That makes it easy to see
// that arr is first generated (by the basic randomizer, with repeats
// possible) and only then corrected by the unique{} constraint in the
// second call -- rather than the uniqueness merely being likely by chance,
// as it would be with a wider element type.
class Foo;
  rand logic [1:0] arr[];
endclass

module t;
  initial begin
    automatic Foo f = new;
    automatic int ok;
    repeat (20) begin
      ok = f.randomize() with {arr.size() == 4;};
      `checkd(ok, 1)
      `checkd(f.arr.size(), 4)

      ok = f.randomize() with {unique {arr};};
      `checkd(ok, 1)
      `checkd(f.arr.size(), 4)
      for (int i = 0; i < 4; i++) begin
        for (int j = i + 1; j < 4; j++) begin
          if (f.arr[i] == f.arr[j]) begin
            $write("%%Error: arr[%0d] == arr[%0d] == %0d, not unique\n", i, j, f.arr[i]);
            `stop;
          end
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
