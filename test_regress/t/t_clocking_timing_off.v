// DESCRIPTION: Verilator: Clocking output skews are ignored where timing is off
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  bit clk;
  bit [1:0] out_v;
  int changes;
  int change_time;

  always #5 clk = ~clk;

  // verilator timing_off
  clocking cb @(posedge clk);
    output #2 out_v;
  endclocking
  // verilator timing_on

  always @(out_v) begin
    if ($time != 0) begin
      ++changes;
      change_time = int'($time);
    end
  end

  initial begin
    @(cb);
    cb.out_v <= 2'd3;
    #10;
    // Without its skew the drive matures in the Re-NBA region of the clocking event
    `checkd(out_v, 3)
    `checkd(changes, 1)
    `checkd(change_time, 5)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
