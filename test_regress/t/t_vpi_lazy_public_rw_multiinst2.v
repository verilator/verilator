// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Two interface instances whose member 'b' is driven from the parent with a
// DIFFERENT same-scope-operand expression per instance (~if0.a vs if1.a^7'h55):
// an operand-only shareability test would wrongly call both shareable.
interface iface2_t;
  logic [6:0] a;
  logic [6:0] b;
endinterface

module t (
  input logic clk,
  input logic rst,
  output logic [6:0] observe
);

  logic [6:0] ctr;

  iface2_t if0();
  iface2_t if1();

  assign if0.a = ctr;
  assign if1.a = ctr + 7'h1;
  assign if0.b = ~if0.a;
  assign if1.b = if1.a ^ 7'h55;

  always_ff @(posedge clk) begin
    if (rst) begin
      ctr <= 7'h0;
      observe <= 7'h0;
    end else begin
      ctr <= ctr + 7'h3;
      observe <= if0.b ^ if1.b;
    end
  end

endmodule
