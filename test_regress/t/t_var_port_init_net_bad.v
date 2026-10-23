// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub (
    output wire y = 1'b1,  // <--- Warning: initialized net
    output tri [1:0] t = 2'b10,  // <--- Warning: initialized net
    output wire logic wl = 1'b1,  // <--- Warning: initialized net
    output var v = 1'b1,
    output logic l = 1'b1,
    input wire i = 1'b1
);
endmodule

module sub_nonansi (
    y
);
  output wire y = 1'b1;  // <--- Warning: initialized net
endmodule

module t;
  wire y, wl, v, l, y2;
  wire [1:0] t;
  sub u_sub (.y(y), .t(t), .wl(wl), .v(v), .l(l));
  sub_nonansi u_sub_nonansi (.y(y2));
endmodule
