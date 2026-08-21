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
class Elem;
  rand int val;
endclass

class Bar;
  rand Elem foo_arr[];
  constraint c_size { foo_arr.size() == 3; }
  function new();
    foo_arr = new[3];
    foreach (foo_arr[i]) foo_arr[i] = new;
  endfunction
endclass

module t;
  initial begin
    automatic Bar bar = new;
    automatic int ok;
    repeat (20) begin
      ok = bar.randomize() with {foreach (foo_arr[i]) foo_arr[i].val < 8;};
      `checkd(ok, 1)
      `checkd(bar.foo_arr.size(), 3)
      foreach (bar.foo_arr[i]) begin
        if (bar.foo_arr[i].val >= 8) begin
          $write("%%Error: foo_arr[%0d].val=%0d not < 8\n", i, bar.foo_arr[i].val);
          `stop;
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
