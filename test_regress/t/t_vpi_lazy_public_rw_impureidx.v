// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Impure bit-select index in always_comb partial write: must be retained.
module t (
  input logic [3:0] data,
  output logic [7:0] obs
);
  logic [31:0] seedv;
  logic [7:0] vec;

  always_comb vec[($random(seedv) & 3) +: 4] = data;

  assign obs = vec;
endmodule
