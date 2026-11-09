// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
module top (
    input clk,
    output logic out
);
  always_ff @(posedge clk) out <= ~out;
  initial begin
    $display("Hello from t_flag_cflags_modules");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
