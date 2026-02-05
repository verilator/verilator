// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  sub sub_default ();
  sub #(.foo_t(logic [7:0])) sub_8 ();

  always @(posedge clk) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module sub #(
    parameter type foo_t = logic,
    parameter type bar_t = foo_t[1:0]
);
  initial begin
    $display("%m foo_t = %0d bar_t = %0d", $bits(foo_t), $bits(bar_t));
    if (2 * $bits(foo_t) != $bits(bar_t)) $stop;
  end
endmodule
