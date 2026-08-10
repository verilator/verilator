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
// arr's element type has only 4 possible values (2'b00-2'b11), so the size
// constraint is kept within that range (2 to 4, rather than a single fixed
// value): any larger and unique{} on a 2-bit array would be unsatisfiable.
// Repeated calls are checked to actually produce more than one size, and
// more than one first-element value, confirming randomize() isn't stuck
// always returning the same solution.
class Foo;
  rand logic [1:0] arr[];
endclass

module t;
  initial begin
    automatic Foo f = new;
    automatic int ok;
    automatic int sz;
    automatic int first_size = -1;
    automatic bit found_size_variety = 0;
    automatic logic [1:0] first_elem = 2'bxx;
    automatic bit found_elem_variety = 0;
    repeat (30) begin
      ok = f.randomize() with {arr.size() inside {[2 : 4]};};
      `checkd(ok, 1)
      sz = f.arr.size();
      if (sz < 2 || sz > 4) begin
        $write("%%Error: arr.size()=%0d not in [2:4]\n", sz);
        `stop;
      end

      ok = f.randomize() with {unique {arr};};
      `checkd(ok, 1)
      `checkd(f.arr.size(), sz)
      if (first_size == -1) first_size = sz;
      else if (sz != first_size) found_size_variety = 1;
      if (first_elem === 2'bxx) first_elem = f.arr[0];
      else if (f.arr[0] !== first_elem) found_elem_variety = 1;
      for (int i = 0; i < sz; i++) begin
        for (int j = i + 1; j < sz; j++) begin
          if (f.arr[i] == f.arr[j]) begin
            $write("%%Error: arr[%0d] == arr[%0d] == %0d, not unique\n", i, j, f.arr[i]);
            `stop;
          end
        end
      end
    end
    if (!found_size_variety) begin
      $write("%%Error: randomize() always produced arr.size()=%0d, no variety across repeats\n",
             first_size);
      `stop;
    end
    if (!found_elem_variety) begin
      $write("%%Error: randomize() always produced arr[0]=%0d, no variety across repeats\n",
             first_elem);
      `stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
