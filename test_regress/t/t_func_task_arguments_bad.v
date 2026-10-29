// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

task dyn_task(input logic [30:0] data[]);
  $display("%p", data);
endtask

task unpacked_task(input logic [30:0] data[3:0]);
  $display("%p", data);
endtask

task queue_task(input logic [30:0] data[$]);
  $display("%p", data);
endtask

task assoc_task(input logic [30:0] data[int]);
  $display("%p", data);
endtask

task scalar_task(input logic data);
  $display("%b", data);
endtask

task scalar_vec_task(input logic [30:0] data);
  $display("%b", data);
endtask

function logic logical_or(input logic a, b);
  return a | b;
endfunction

module t;
  logic unpacked_data[3:0];
  logic dyn_data[];
  logic queue_data[$];
  logic assoc_data[int];
  logic vec_data[3:0];
  logic my_signal_a[10];
  logic my_signal_b[10];
  initial begin
    dyn_task(.data($urandom));
    unpacked_task(.data($urandom));
    queue_task(.data($urandom));
    assoc_task(.data($urandom));
    scalar_task(.data(unpacked_data));
    scalar_task(.data(dyn_data));
    scalar_task(.data(queue_data));
    scalar_task(.data(assoc_data));
    scalar_vec_task(.data(vec_data));
    logical_or(my_signal_a[0], my_signal_b);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
