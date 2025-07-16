// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  wire u1;
  wire u2;
  wire u3;
  wire u4;
  wire u5;
  wire u6;

  pullup (supply1) pu1(a);
  pullup (strong1) pu2(a);
  pullup (pull1) pu3(a);
  pullup (weak1) pu4(a);
  pullup (supply1, supply0) pu5(a);
  pullup (strong0, strong1) pu6(a);

  wire d1;
  wire d2;
  wire d3;
  wire d4;
  wire d5;
  wire d6;

  pulldown (supply0) pd1(a);
  pulldown (strong0) pd2(a);
  pulldown (pull0) pd3(a);
  pulldown (weak0) pd4(a);
  pulldown (supply0, supply1) pd5(a);
  pulldown (strong1, strong0) pd6(a);

endmodule
