// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2006 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  sub sub ();

  integer cyc = 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) begin
      // Not $finish; as we don't want a message to scroll by
      $c("Verilated::threadContextp()->gotFinish(true);");
    end
  end
endmodule

module sub;
  /* verilator no_inline_module */
endmodule
