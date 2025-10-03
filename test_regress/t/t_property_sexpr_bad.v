// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;
  bit val;

  always @(negedge clk) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

  assert property (@(posedge clk) ##1 not val) $display("[%0t] single delay with negated var stmt, fileline:%d", $time, `__LINE__);
endmodule
