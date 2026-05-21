// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns / 1ns
module t;
  semaphore sem = new(1);
  integer i;

  task driver;
    repeat (3) begin
      sem.get(1);
      $display("[%0t] DRV locked", $time);
      #5 sem.put(1);
      $display("[%0t] DRV unlocked", $time);
    end
  endtask

  task monitor;
    for (i = 0; i < 3; i = i + 1) begin
      #1 sem.get(1);
      $display("[%0t] MON locked", $time);
      sem.put(1);
      $display("[%0t] MON unlocked", $time);
    end
  endtask

  initial begin
    fork
      driver();
      monitor();
    join
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
