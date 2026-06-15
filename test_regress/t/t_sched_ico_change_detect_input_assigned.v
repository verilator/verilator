// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t(
  clk, i, o, cyc
);

  input clk, i;
  output o, cyc;

  logic   clk;
  int     i; // Primary input that the design also drives
  int     o;
  int     cyc = 0;

  // Logic dependent on primary input 'i'
  always_comb  o = i + 10;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    // On even cycles, assign 'i'
    if (cyc % 2 == 0) i = cyc + 1000;
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
