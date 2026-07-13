// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Impure and variable-index drivers must be retained (not reconstructed).
module t (
  input logic [2:0] idx,
  input logic [3:0] nib
);
  // Impure driver: not reconstructable, retained.
  logic [31:0] seed;
  logic [31:0] rnd;
  assign rnd = $random(seed);

  // Variable index partial write: not reconstructable, retained.
  logic [7:0] base;
  assign base[idx +: 4] = nib;
endmodule
