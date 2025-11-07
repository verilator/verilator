// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface intf
#(
  parameter int FOO = 32
)
();
endinterface

module sub (
  intf intf_a,
  intf intf_b
);
  localparam int INTF_A_FOO = intf_a.FOO;
  localparam int INTF_B_FOO = intf_b.FOO;
  if (INTF_A_FOO != INTF_B_FOO)
    $error("INTF_A_FOO != INTF_B_FOO: %0d != %0d", INTF_A_FOO, INTF_B_FOO);
endmodule

module t;
  intf #(.FOO (21)) local_intf ();
  /* verilator lint_off HIERPARAM */
`ifdef CONST_LITERAL
  intf #(.FOO(21)) the_intf_a ();
`else
`ifdef INTERMEDIATE_LPARAM
  localparam int LOCAL_INTF_FOO = local_intf.FOO;
  intf #(.FOO(LOCAL_INTF_FOO)) the_intf_a ();
`else
  intf #(.FOO(local_intf.FOO)) the_intf_a ();
`endif
`endif
  /* verilator lint_on HIERPARAM */
  intf #(.FOO(21)) the_intf_b ();

  sub the_sub (
    .intf_a (the_intf_a),
    .intf_b (the_intf_b));
endmodule
