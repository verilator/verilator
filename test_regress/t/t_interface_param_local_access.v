// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface intf #(
    parameter int FOO = 32
) ();
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
  intf #(.FOO(21)) local_intf ();

  intf #(.FOO(21)) intf_a_1 ();
  intf #(.FOO(21)) intf_b_1 ();
  sub sub_1 (
      .intf_a(intf_a_1),
      .intf_b(intf_b_1)
  );

  /* verilator lint_off HIERPARAM */
  localparam int LOCAL_INTF_FOO = local_intf.FOO;
  /* verilator lint_on HIERPARAM */
  intf #(.FOO(LOCAL_INTF_FOO)) intf_a_2 ();
  intf #(.FOO(21)) intf_b_2 ();
  sub sub_2 (
      .intf_a(intf_a_2),
      .intf_b(intf_b_2)
  );

  /* verilator lint_off HIERPARAM */
  intf #(.FOO(local_intf.FOO)) intf_a_3 ();
  /* verilator lint_on HIERPARAM */
  intf #(.FOO(21)) intf_b_3 ();
  sub sub_3 (
      .intf_a(intf_a_3),
      .intf_b(intf_b_3)
  );

endmodule
