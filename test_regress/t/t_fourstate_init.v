// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module sub(input [95:0] notTopLvlInput, input notTopLvlInputs);
  initial begin
    if (notTopLvlInput !== 96'bz) $stop;
    if (notTopLvlInputs !== 1'bz) $stop;
  end
endmodule

module t(input [95:0] topLvlInput, input topLvlInputs);
  reg [95:0]  r;
  reg rs;
  wire [95:0] w;
  wire ws;
  logic [95:0] l;
  logic ls;
  logic [96:0] l2;

  // verilator lint_off PINMISSING
  sub s();
  // verilator lint_on PINMISSING

  initial begin
    logic [127:0] tmp;
    if (topLvlInput !== 96'b0) $stop;
    if (topLvlInputs !== 1'b0) $stop;
    if (r !== 96'bx) $stop;
    if (rs !== 1'bx) $stop;
    if (w !== 96'bz) $stop;
    if (ws !== 1'bz) $stop;
    if (ls !== 1'bx) $stop;
    if (l2 !== 97'bx) $stop;
    // verilator lint_off WIDTHEXPAND
    tmp = l2;   // To check weather bits are clean
    // verilator lint_on WIDTHEXPAND
    if (tmp !== {{31'd0, 97'bx}}) $stop;
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
