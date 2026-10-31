// DESCRIPTION: Verilator: Count suspendable DPI exports
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  export "DPI-C" task export_delay;
  task automatic export_delay();
    #1;
  endtask

  export "DPI-C" task export_event;
  task automatic export_event();
    @(posedge clk);
  endtask

  export "DPI-C" task export_wait;
  task automatic export_wait();
    wait (clk);
  endtask

  export "DPI-C" task export_no_delay;
  task automatic export_no_delay();
      $display("No delay\n");
  endtask

  bit clk = 0;
  initial begin
    #1 clk = 1;
    $finish;
  end
endmodule
