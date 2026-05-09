// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Negative test: a paramed-class static function call used directly as the
// parameter argument to another paramed class is not currently supported.
// Folding the function call to a constant during specialization requires
// constant-function evaluation that this fix does not provide.

class C #(parameter int a = 0);
  static function int get_a();
    return a;
  endfunction
endclass

class D #(parameter int v = 0);
  localparam int x = v;
endclass

module t;
  localparam int y = D#(C#(7)::get_a())::x;
endmodule
