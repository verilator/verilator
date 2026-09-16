// DESCRIPTION: Verilator: Timed tristate assignments within one procedural block
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  logic source = 1'b1;
  logic [1:0] blocking_result;
  logic [1:0] nba_result;

  initial begin
    blocking_result = 'z;

    // The RHS, including whether it drives Z, is sampled before the delay.
    blocking_result[0] = #2 source ? 1'b1 : 1'bz;
    #1;
    `checkh(blocking_result, 2'bz1);
    blocking_result[1] = #1 1'b1;
    #1;
    `checkh(blocking_result, 2'b11);
    blocking_result[0] = #1 1'bz;
    #1;
    `checkh(blocking_result, 2'b1z);

    nba_result = 'z;
    nba_result[0] <= #1 1'b1;
    nba_result[1] <= #1 1'b1;
    #2;
    `checkh(nba_result, 2'b11);
    nba_result[0] <= #1 1'bz;
    nba_result[1] <= #1 1'b0;
    #2;
    `checkh(nba_result, 2'b0z);

    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    #1 source = 1'b0;
  end

endmodule
