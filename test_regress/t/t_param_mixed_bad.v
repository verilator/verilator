// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub #(
    parameter A = 1,
    parameter B = 2
);
endmodule

interface ifc #(
    parameter A = 1,
    parameter B = 2
);
endinterface

class Cls #(
    parameter A = 1,
    parameter B = 2
);
endclass

module t;
  sub #(10, .B(15)) u_ordered_named ();  // Bad
  sub #(.A(10), 15) u_named_ordered ();  // Bad
  sub #(10, 15) u_ordered ();
  sub #(.A(10), .B(15)) u_named ();
  ifc #(10, .B(15)) i_ordered_named ();  // Bad
  Cls #(10, .B(15)) c_ordered_named;  // Bad
endmodule
