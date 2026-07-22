// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

task dyn_task(input logic [30:0] data []);
  $display("%p", data);
endtask

task unpacked_task(input logic [30:0] data [3:0]);
  $display("%p", data);
endtask

task queue_task(input logic [30:0] data [$]);
  $display("%p", data);
endtask

task assoc_task(input logic [30:0] data [int]);
  $display("%p", data);
endtask

module t;
  initial begin
    dyn_task(.data($urandom));
    unpacked_task(.data($urandom));
    queue_task(.data($urandom));
    assoc_task(.data($urandom));
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
