// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input wire clk,
    input wire reset,
    output logic v,
    output logic w
);
  // A conflict between two processes is still reported when a task definition
  // writes the same variable, but the definition is not the other write.

  always_ff @(posedge clk) v <= 1'b0;  // <--- Location of other write

  task automatic set_v;
    v <= 1'b1;
  endtask

  always_ff @(posedge reset) v <= 1'b1;  // <--- Warning

  // With the call seen before the definition, the call site is the other write.

  always_ff @(posedge clk) set_w();  // <--- Location of other write

  task automatic set_w;
    w <= 1'b1;
  endtask

  always_ff @(posedge reset) w <= 1'b0;  // <--- Warning

endmodule
