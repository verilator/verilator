// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

class monitor;
  bit clk, enable, fired;
  task run();
    forever @(posedge clk iff enable) fired = 1;
  endtask
endclass

module t;
  monitor mon = new;
  always #5 mon.clk = ~mon.clk;
  initial begin
    fork
      mon.run();
    join_none

    repeat (4) @(posedge mon.clk);
    if (mon.fired !== 0) begin
      $display("FAIL: fired before iff guard satisfied");
      $stop;
    end

    mon.enable = 1;
    repeat (2) @(posedge mon.clk);
    if (mon.fired !== 1) begin
      $display("FAIL: did not fire when guard true");
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
