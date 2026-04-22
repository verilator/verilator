// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`ifdef VERILATOR
`define IMPURE_ONE ($c(1))
`else
`define IMPURE_ONE (|($random | $random))
`endif

module t;
  function integer f(integer x);
    if (`IMPURE_ONE) return x;
    return 'x;
  endfunction
  function logic [31:0] g(logic [31:0] x);
    if (`IMPURE_ONE) return x;
    return 'x;
  endfunction

  initial begin
    if ((f('b1) == f('b1)) !== 1'b1) $stop;
    if ((f('b1) == f('b0)) !== 1'b0) $stop;
    if ((f('b0) == f('b0)) !== 1'b1) $stop;
    if ((f('b0) == f('b1)) !== 1'b0) $stop;
    if ((f('b0) == f('bx)) !== 1'bx) $stop;
    if ((f('b0) == f('bx)) !== 1'bx) $stop;
    if ((f('b1) == f('bx)) !== 1'bx) $stop;
    if ((f('bx) == f('bx)) !== 1'bx) $stop;
    if ((f('bx) == f('bz)) !== 1'bx) $stop;
    if ((f('bz) == f('bz)) !== 1'bx) $stop;
    if ((f('bz) == f('b1)) !== 1'bx) $stop;
    if ((f('bz) == f('b0)) !== 1'bx) $stop;

    if ((f('b1) != f('b1)) !== 1'b0) $stop;
    if ((f('b1) != f('b0)) !== 1'b1) $stop;
    if ((f('b0) != f('b0)) !== 1'b0) $stop;
    if ((f('b0) != f('b1)) !== 1'b1) $stop;
    if ((f('b0) != f('bx)) !== 1'bx) $stop;
    if ((f('b0) != f('bx)) !== 1'bx) $stop;
    if ((f('b1) != f('bx)) !== 1'bx) $stop;
    if ((f('bx) != f('bx)) !== 1'bx) $stop;
    if ((f('bx) != f('bz)) !== 1'bx) $stop;
    if ((f('bz) != f('bz)) !== 1'bx) $stop;
    if ((f('bz) != f('b1)) !== 1'bx) $stop;
    if ((f('bz) != f('b0)) !== 1'bx) $stop;

    if ((f('b1) < f('b1)) !== 1'b0) $stop;
    if ((f('b1) < f('b0)) !== 1'b0) $stop;
    if ((f('b0) < f('b0)) !== 1'b0) $stop;
    if ((f('b0) < f('b1)) !== 1'b1) $stop;
    if ((f('b0) < f('bx)) !== 1'bx) $stop;
    if ((f('b0) < f('bx)) !== 1'bx) $stop;
    if ((f('b1) < f('bx)) !== 1'bx) $stop;
    if ((f('bx) < f('bx)) !== 1'bx) $stop;
    if ((f('bx) < f('bz)) !== 1'bx) $stop;
    if ((f('bz) < f('bz)) !== 1'bx) $stop;
    if ((f('bz) < f('b1)) !== 1'bx) $stop;
    if ((f('bz) < f('b0)) !== 1'bx) $stop;

    if ((f('b1) <= f('b1)) !== 1'b1) $stop;
    if ((f('b1) <= f('b0)) !== 1'b0) $stop;
    if ((f('b0) <= f('b0)) !== 1'b1) $stop;
    if ((f('b0) <= f('b1)) !== 1'b1) $stop;
    if ((f('b0) <= f('bx)) !== 1'bx) $stop;
    if ((f('b0) <= f('bx)) !== 1'bx) $stop;
    if ((f('b1) <= f('bx)) !== 1'bx) $stop;
    if ((f('bx) <= f('bx)) !== 1'bx) $stop;
    if ((f('bx) <= f('bz)) !== 1'bx) $stop;
    if ((f('bz) <= f('bz)) !== 1'bx) $stop;
    if ((f('bz) <= f('b1)) !== 1'bx) $stop;
    if ((f('bz) <= f('b0)) !== 1'bx) $stop;

    if ((f('b1) > f('b1)) !== 1'b0) $stop;
    if ((f('b1) > f('b0)) !== 1'b1) $stop;
    if ((f('b0) > f('b0)) !== 1'b0) $stop;
    if ((f('b0) > f('b1)) !== 1'b0) $stop;
    if ((f('b0) > f('bx)) !== 1'bx) $stop;
    if ((f('b0) > f('bx)) !== 1'bx) $stop;
    if ((f('b1) > f('bx)) !== 1'bx) $stop;
    if ((f('bx) > f('bx)) !== 1'bx) $stop;
    if ((f('bx) > f('bz)) !== 1'bx) $stop;
    if ((f('bz) > f('bz)) !== 1'bx) $stop;
    if ((f('bz) > f('b1)) !== 1'bx) $stop;
    if ((f('bz) > f('b0)) !== 1'bx) $stop;

    if ((f('b1) >= f('b1)) !== 1'b1) $stop;
    if ((f('b1) >= f('b0)) !== 1'b1) $stop;
    if ((f('b0) >= f('b0)) !== 1'b1) $stop;
    if ((f('b0) >= f('b1)) !== 1'b0) $stop;
    if ((f('b0) >= f('bx)) !== 1'bx) $stop;
    if ((f('b0) >= f('bx)) !== 1'bx) $stop;
    if ((f('b1) >= f('bx)) !== 1'bx) $stop;
    if ((f('bx) >= f('bx)) !== 1'bx) $stop;
    if ((f('bx) >= f('bz)) !== 1'bx) $stop;
    if ((f('bz) >= f('bz)) !== 1'bx) $stop;
    if ((f('bz) >= f('b1)) !== 1'bx) $stop;
    if ((f('bz) >= f('b0)) !== 1'bx) $stop;

    // Unsigned
    if ((g('b1) < g('b1)) !== 1'b0) $stop;
    if ((g('b1) < g('b0)) !== 1'b0) $stop;
    if ((g('b0) < g('b0)) !== 1'b0) $stop;
    if ((g('b0) < g('b1)) !== 1'b1) $stop;
    if ((g('b0) < g('bx)) !== 1'bx) $stop;
    if ((g('b0) < g('bx)) !== 1'bx) $stop;
    if ((g('b1) < g('bx)) !== 1'bx) $stop;
    if ((g('bx) < g('bx)) !== 1'bx) $stop;
    if ((g('bx) < g('bz)) !== 1'bx) $stop;
    if ((g('bz) < g('bz)) !== 1'bx) $stop;
    if ((g('bz) < g('b1)) !== 1'bx) $stop;
    if ((g('bz) < g('b0)) !== 1'bx) $stop;

    if ((g('b1) <= g('b1)) !== 1'b1) $stop;
    if ((g('b1) <= g('b0)) !== 1'b0) $stop;
    if ((g('b0) <= g('b0)) !== 1'b1) $stop;
    if ((g('b0) <= g('b1)) !== 1'b1) $stop;
    if ((g('b0) <= g('bx)) !== 1'bx) $stop;
    if ((g('b0) <= g('bx)) !== 1'bx) $stop;
    if ((g('b1) <= g('bx)) !== 1'bx) $stop;
    if ((g('bx) <= g('bx)) !== 1'bx) $stop;
    if ((g('bx) <= g('bz)) !== 1'bx) $stop;
    if ((g('bz) <= g('bz)) !== 1'bx) $stop;
    if ((g('bz) <= g('b1)) !== 1'bx) $stop;
    if ((g('bz) <= g('b0)) !== 1'bx) $stop;

    if ((g('b1) > g('b1)) !== 1'b0) $stop;
    if ((g('b1) > g('b0)) !== 1'b1) $stop;
    if ((g('b0) > g('b0)) !== 1'b0) $stop;
    if ((g('b0) > g('b1)) !== 1'b0) $stop;
    if ((g('b0) > g('bx)) !== 1'bx) $stop;
    if ((g('b0) > g('bx)) !== 1'bx) $stop;
    if ((g('b1) > g('bx)) !== 1'bx) $stop;
    if ((g('bx) > g('bx)) !== 1'bx) $stop;
    if ((g('bx) > g('bz)) !== 1'bx) $stop;
    if ((g('bz) > g('bz)) !== 1'bx) $stop;
    if ((g('bz) > g('b1)) !== 1'bx) $stop;
    if ((g('bz) > g('b0)) !== 1'bx) $stop;

    if ((g('b1) >= g('b1)) !== 1'b1) $stop;
    if ((g('b1) >= g('b0)) !== 1'b1) $stop;
    if ((g('b0) >= g('b0)) !== 1'b1) $stop;
    if ((g('b0) >= g('b1)) !== 1'b0) $stop;
    if ((g('b0) >= g('bx)) !== 1'bx) $stop;
    if ((g('b0) >= g('bx)) !== 1'bx) $stop;
    if ((g('b1) >= g('bx)) !== 1'bx) $stop;
    if ((g('bx) >= g('bx)) !== 1'bx) $stop;
    if ((g('bx) >= g('bz)) !== 1'bx) $stop;
    if ((g('bz) >= g('bz)) !== 1'bx) $stop;
    if ((g('bz) >= g('b1)) !== 1'bx) $stop;
    if ((g('bz) >= g('b0)) !== 1'bx) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
