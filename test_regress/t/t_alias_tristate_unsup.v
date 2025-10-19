// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  wire [31:0] a, b;

  integer cyc = 0;
  assign a = 'z;
  alias a = b;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (a !== 'z) $stop;
    if (b !== 'z) $stop;

    $write("*-* All Finished *-*\n");
    $finish;

  end
endmodule
