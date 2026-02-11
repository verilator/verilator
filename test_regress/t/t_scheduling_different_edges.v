// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module x;
  bit val = 0;
  bit ok = 0;

  initial #1 begin
    val = 1;
    @(val);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial @(posedge val) begin
    val = 0;
    ok = 1;
    @(edge val);
    $stop;
  end
  initial #10 $stop;
endmodule
