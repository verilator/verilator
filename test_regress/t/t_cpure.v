// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional transitive alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

function int func();
  $cpure("const auto x = 13;");
  $cpure("auto y = 4;");
  $cpure("++y;");
  $cpure("const auto res = x + y;");
  return $cpure("res");
endfunction

module t;
  initial begin
    if (func() != 18) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
