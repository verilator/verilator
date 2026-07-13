// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Explicit public_flat_rw vs lazy reconstruction.
module t (
  input  logic [7:0] a,
  output logic [7:0] obs
);

  // Pinned read-write with storage.
  logic [7:0] pinned_rw /* verilator public_flat_rw */;
  assign pinned_rw = a ^ 8'h5;

  // Reconstructed read-only.
  logic [7:0] lazy_ro;
  assign lazy_ro = a + 8'h1;

  assign obs = pinned_rw ^ lazy_ro;

endmodule
