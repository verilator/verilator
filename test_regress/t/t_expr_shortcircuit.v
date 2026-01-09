// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc = 0;

  function automatic logic is_odd(int value);
    logic odd = value % 2 == 1;
    if (!odd) $error($sformatf("%0d is not odd", value));
    return odd;
  endfunction

  always_ff @(posedge clk) begin
    if (cyc[0] == 1'b0 || is_odd(cyc)) cyc <= cyc + 1;
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
