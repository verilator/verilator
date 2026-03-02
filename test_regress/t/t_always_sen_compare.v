// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module top;
  sub inst (
      .a({128{1'b1}}),
      .b({128{1'b1}})
  );
endmodule

module sub (
    a,
    b
);
  input [127:0] a;
  input [127:0] b;
  always @(a or b) begin
    $display("doesn't matter");
  end
endmodule
