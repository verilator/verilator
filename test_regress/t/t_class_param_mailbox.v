// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub #(
    parameter type T = logic
);
  mailbox #(T) mbox;
endmodule

module try #(
    parameter I = 1
);
endmodule

module t;
  typedef struct packed {
    logic a;
    logic b;
  } my_struct_t;

  sub #(my_struct_t) u_sub ();
  try #(2) u_try2 ();

  initial $finish;

endmodule
