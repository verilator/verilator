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

  wire [15:0] a, b;

  integer cyc = 0;

  alias a = b;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) begin
      force a = 16'h1234;
      if (a != 16'h1234 || a != b) $stop;
      release a;
    end
    else if (cyc == 2) begin
      force b = 16'h5678;
      if (a != 16'h5678 || a != b) $stop;
      release b;
    end
    else if (cyc == 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
