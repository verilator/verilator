// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off PINNOTFOUND */

module child ();
endmodule

module t;
  child u_child (
    .missing_port (1'b0)
  );
endmodule
