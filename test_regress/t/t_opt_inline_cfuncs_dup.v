// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  integer cyc = 0;

  task automatic tick();
    // verilator no_inline_task
    automatic time t = $time;
    $display("TICK: %0t", t);
  endtask

  always @(posedge clk) begin
    cyc <= cyc + 1;
    tick();
    tick();
    tick();
    tick();
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
