// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Multidriven and reconstructed signal retention checks.
module t (
  input logic [7:0] a,
  input logic [7:0] b,
  output logic [7:0] o
);
  // Multidriven w (retained); reconstructed r.
  logic [7:0] w;
  assign w = a;
  assign w = b;

  logic [7:0] r;
  assign r = a & b;

  assign o = w ^ r;
endmodule
