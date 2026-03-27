// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  function logic f(logic a);
    if (a === 1'b1) $write("1");
    else if (a === 1'b0) $write("0");
    else if (a === 1'bx) $write("x");
    else if (a === 1'bz) $write("z");
    else $stop;
    $write("\n");
    return a;
  endfunction

  initial begin
    if ((
      ((f(1) ? f(1) : f('z)) && (f('x) ? f(1) : f(0))) ?
      (((f(1) || f('z)) && (f('x))) && ((f(0) ? f('x) : f(0)))) :
      ((f('x) || f(0)) && (f(0) || (f('z) && (f(0) && f('z))))
      )) !== 0) begin
        $stop;
      end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
