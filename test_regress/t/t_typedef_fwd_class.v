// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef logic [3:0] T;

class Cls;
  extern static function int f(T x);
  // This is after the usage above, but to match other simulators,
  // no error about use after declaration
  typedef logic [7:0] T;
endclass
function int Cls::f(T x);
  return $bits(x);
endfunction

module t;
  initial begin
    if (Cls::f('1) != 8) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
