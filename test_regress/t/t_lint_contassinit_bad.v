// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Zhi QU
// SPDX-License-Identifier: CC0-1.0

interface decoupled_ifc;
  logic ready;
endinterface

module t (
    output wire out
);

  logic a = 1'b0;  // declaration initialization
  assign a = 1'b1;  // continuous assignment

  assign out = a;

  // OK as two different instances
  decoupled_ifc ifc_in ();
  decoupled_ifc ifc_out ();
  initial ifc_out.ready = 0;
  assign ifc_in.ready = ifc_out.ready;

endmodule
