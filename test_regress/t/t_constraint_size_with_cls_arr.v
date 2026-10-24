// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Francesco Urbani
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A dynamic array of class-typed elements, sized by a class-level
// constraint, referenced (not via unique{}) by an unrelated randomize()
// with {} block. The with-block's two-phase solve refresh loop must skip
// write_var'ing the array itself (its elements are separately randomized
// sub-objects, passed to the solver as their own variables) rather than
// trying to pass the whole array to the solver.
//
// The size is kept at a single fixed value here deliberately, unlike the
// other tests in this family: letting it vary across repeated calls means
// it can shrink and later grow back, and growing a dynamic array of class
// handles back up exposes the newly-grown slots as null (destroyed on
// shrink, never reconstructed) -- a separate, pre-existing gotcha in
// class-typed array randomization, not something this fix touches. Variety
// across repeated calls is instead checked on the (always safely
// re-randomized) element field.
class Elem;
  rand int val;
endclass

class Bar;
  rand Elem foo_arr[];
  constraint c_size {foo_arr.size() == 3;}
  function new();
    foo_arr = new[3];
    foreach (foo_arr[i]) foo_arr[i] = new;
  endfunction
endclass

module t;
  initial begin
    automatic Bar bar = new;
    automatic int ok;
    automatic int first_val = -1;
    automatic bit found_variety = 0;
    repeat (30) begin
      ok = bar.randomize() with {foreach (foo_arr[i]) foo_arr[i].val < 8;};
      `checkd(ok, 1)
      `checkd(bar.foo_arr.size(), 3)
      if (first_val == -1) first_val = bar.foo_arr[0].val;
      else if (bar.foo_arr[0].val != first_val) found_variety = 1;
      foreach (bar.foo_arr[i]) begin
        if (bar.foo_arr[i].val >= 8) begin
          $write("%%Error: foo_arr[%0d].val=%0d not < 8\n", i, bar.foo_arr[i].val);
          `stop;
        end
      end
    end
    if (!found_variety) begin
      $write("%%Error: randomize() always produced foo_arr[0].val=%0d, no variety across repeats\n",
             first_val);
      `stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
