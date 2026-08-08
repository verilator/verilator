// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Completeness floor: retains undriven residuals vs lazy reconstruction.
module t (
  input logic [7:0] a,
  output logic [7:0] o
);
  // Sole pure driver: reconstructed (not retained).
  logic [7:0] recon;
  assign recon = a + 8'd1;

  // Undriven/unread: floor retains, plain lazy drops.
  logic [7:0] orphan;

  assign o = recon;
endmodule
