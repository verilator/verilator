// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional transitive alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

function int func();
  static int someVar = 12;
  return $cpure(someVar, "+ 6");
endfunction

module t;
  initial begin
    if (func() != 18) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
