// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

`define stop $stop

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  int cyc = 0;
  int status;
  logic toggler = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    toggler <= cyc[0];
    // Counts before the last reset are dropped
    if (cyc == 3) $coverage_control(`SV_COV_RESET, `SV_COV_ALL, `SV_COV_HIER, $root);
    if (cyc == 5) begin
      status = $coverage_control(`SV_COV_RESET, `SV_COV_ALL, `SV_COV_HIER, $root);
`ifdef NO_COVERAGE
      if (status != `SV_COV_NOCOV) `stop;
`else
      if (status != `SV_COV_OK) `stop;
`endif
    end
    if (cyc == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
