// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Graeme Smecher
// SPDX-License-Identifier: CC0-1.0

module t (
    input wire a,
    output wire y
);
  wire w = a;
  out_z out_z (
      .p(w),
      .y(y)
  );
  pass pass (
      .a(),
      .b(),
      .s(),
      .u()
  );
endmodule

module out_z (
    output wire p,  // Tested for Z, never driven here
    output wire y
);
  assign y = (p === 1'bz);
endmodule

// Input ports passed on to a port tested for Z by an expression that can carry Z
module pass (
    input wire a,
    input wire [1:0] b,
    input wire signed s,
    input wire u[2]
);
  zt2 zt2_extend (.i(2'(a)));
  zt2 zt2_extends (.i(2'(s)));
  zt2 zt2_replicate (.i({2{a}}));
  zt2 zt2_shiftl (.i(b << 1));
  zt2 zt2_shiftr (.i(b >> 1));
  zt2 zt2_shiftrs (.i(2'(s) >>> 1));
  zt2 zt2_arraysel (.i({a, u[0]}));
  zt2 zt2_streaml (.i({<<{b}}));
  zt2 zt2_streamr (.i({>>{b}}));
  zt2 zt2_xref (.i({a, pass.a}));
endmodule

module zt2 (
    input wire [1:0] i
);
  wire [1:0] z;
  assign z[0] = (i[0] === 1'bz);
  assign z[1] = (i[1] === 1'bz);
endmodule
