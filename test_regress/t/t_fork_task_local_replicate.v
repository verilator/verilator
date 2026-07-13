// DESCRIPTION: Verilator: Task-local variables survive scheduler logic replication
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic a,
    output logic unused
);

  task automatic spawn(input logic value);
    fork
      unused = value;
    join_none
  endtask

  always @* spawn(a);

endmodule
