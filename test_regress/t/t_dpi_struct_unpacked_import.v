// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Only imports pass unpacked structures, declared in the compilation unit

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {
  int a;
  int b[2];
} unit_t;
import "DPI-C" function int dpii_unit(
  input unit_t i,
  output unit_t o
);

module t;
  initial begin
    unit_t i;
    unit_t o;
    i = '{a: 1, b: '{2, 3}};
    `checkd(dpii_unit(i, o), 6);
    `checkd(o.a, 2);
    `checkd(o.b[0], 3);
    `checkd(o.b[1], 4);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
