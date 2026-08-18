// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input int step
);

  logic [7:0] mem[0:1];

  always @(posedge clk) begin
    case (step)
      1: $readmemh("t_verilated_user_hooks_no_such_file.mem", mem);
      2: $stop;
      3: $fatal(0, "user hook fatal");
      4: $finish;
      default: ;
    endcase
  end

endmodule
