// DESCRIPTION: Verilator: Verilog Test module
//
// Test modport export task with prototype, out-of-block definition,
// and cross-module call via import (IEEE 1800-2017 25.4, 25.8).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

interface bus_if;
  logic [7:0] data;
  logic [7:0] result;

  modport provider(
    output data,
    output result,
    export task send(input logic [7:0] val),
    export task accumulate(input logic [7:0] a, input logic [7:0] b)
  );

  modport consumer(
    input data,
    input result,
    import task send(input logic [7:0] val),
    import task accumulate(input logic [7:0] a, input logic [7:0] b)
  );
endinterface

module driver(bus_if.provider port);
  // Out-of-block task definition for exported 'send' (IEEE 25.8)
  task port.send(input logic [7:0] val);
    port.data = val;
  endtask

  // Out-of-block task definition for exported 'accumulate'
  task port.accumulate(input logic [7:0] a, input logic [7:0] b);
    port.result = a + b;
  endtask
endmodule

module t;
  bus_if bif();
  driver drv(.port(bif.provider));

  initial begin
    // Test 1: simple value passing via export task
    bif.consumer.send(8'hAB);
    if (bif.data !== 8'hAB) begin
      $display("%%Error: Test 1 FAIL: expected AB, got %0h", bif.data);
      $stop;
    end

    // Test 2: second call with different value
    bif.consumer.send(8'h42);
    if (bif.data !== 8'h42) begin
      $display("%%Error: Test 2 FAIL: expected 42, got %0h", bif.data);
      $stop;
    end

    // Test 3: accumulate task with two arguments
    bif.consumer.accumulate(8'h10, 8'h20);
    if (bif.result !== 8'h30) begin
      $display("%%Error: Test 3 FAIL: expected 30, got %0h", bif.result);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
