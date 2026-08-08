// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// One interface class, three instances. `val` is driven from the parent scope
// with a DIFFERENT cone per instance (two cross-scope, one constant tie), so a
// single shared per-class reconstruct function cannot represent all three: it
// must be retained (eager) per instance. `derived` is a class-internal cone,
// identical across instances, and must still reconstruct correctly per instance.
interface iface_t;
  logic [6:0] val;
  logic [6:0] derived;
  assign derived = val + 7'h1;
endinterface

module t (
  input logic clk,
  input logic rst,
  output logic [6:0] observe
);

  logic [6:0] ctr;

  iface_t if_a();
  iface_t if_b();
  iface_t if_c();

  assign if_a.val = ctr + 7'h1;
  assign if_b.val = ctr ^ 7'h2a;
  assign if_c.val = 7'h55;

  always_ff @(posedge clk) begin
    if (rst) begin
      ctr <= 7'h0;
      observe <= 7'h0;
    end else begin
      ctr <= ctr + 7'h3;
      observe <= if_a.derived ^ if_b.derived ^ if_c.derived;
    end
  end

endmodule
