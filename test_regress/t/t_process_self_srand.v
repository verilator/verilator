// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`ifdef verilator
 `define optimize_barrier $c("/*IMPURITY*/")
`else
 `define optimize_barrier
`endif
// verilog_format: on

module t;
  function process p();
    `optimize_barrier;
    return process::self();
  endfunction

  initial begin
    int x;
    int y;
    process::self().srandom(7);
    x = $urandom();
    y = $urandom();
    if (x == y) $stop;
    p().srandom(7);
    y = $urandom();
    if (x != y) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
