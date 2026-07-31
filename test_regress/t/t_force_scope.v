// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module child (
    input wire i
);
  /*verilator no_inline_module*/

  logic [2:0] unpacked[2] = '{3'b001, 3'b010};
endmodule

module t;
  child a (.i(1'b0));
  child b (.i(1'b0));

  initial begin
    force a.i = 1'b1;
    force a.unpacked[0] = 3'b111;

    if (a.i !== 1'b1) $stop;
    if (b.i !== 1'b0) $stop;
    if (a.i === b.i) $stop;
    if (a.unpacked[0] !== 3'b111) $stop;
    if (b.unpacked[0] !== 3'b001) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
