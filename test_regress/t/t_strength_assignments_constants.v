// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
  wire a;
  assign (weak0, weak1) a = 1;
  assign (weak0, supply1) a = 1;
  assign (strong0, strong1) a = 0;

  wire (weak0, weak1) b = 1;
  assign (strong0, strong1) b = 0;

  wire [1:0] c;
  assign (weak0, supply1) c = 2'b11;
  assign (supply0, pull1) c = 2'b11;
  assign (strong0, strong1) c = 0;

  wire [1:0] cr;
  assign (supply1, weak0) cr = 2'b11;
  assign (pull1, supply0) cr = 2'b11;
  assign (strong1, strong0) cr = 0;

  supply0 d;
  assign (strong0, strong1) d = 1;

  wire (supply0, supply1) e = 1'bz;
  assign (weak0, weak1) e = 1;

  always begin
    if (a !== 1'b1) $stop;
    if (b !== 1'b0) $stop;
    if (c !== 2'b11) $stop;
    if (cr !== 2'b11) $stop;
    if (e !== 1'b1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
