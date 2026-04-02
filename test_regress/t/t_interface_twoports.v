// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface A;
  logic x;
endinterface

module B;
  A a ();
endmodule

module C (
    A a0,
    A a1
);
  assign a1.x = a0.x;
endmodule

module t;
  B b0 ();
  B b1 ();
  C c (
      b0.a,
      b1.a
  );
  initial $finish;
endmodule
