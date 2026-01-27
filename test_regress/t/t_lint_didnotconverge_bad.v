// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
  // Outputs
  a, b
  );

  // verilator lint_off UNOPTFLAT

  output logic a, b;

  always_comb b = ~a;
  always_comb a = b;

endmodule
