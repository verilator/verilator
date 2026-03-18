// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

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
  task port.send(input logic [7:0] val);
    port.data = val;
    port.result = val + 8'h01;
  endtask

  task port.accumulate(input logic [7:0] a, input logic [7:0] b);
    port.data = a;
    port.result = a + b;
  endtask
endmodule

module t;
  bus_if bif();
  driver drv(.port(bif.provider));

  initial begin
    // Test 1: send -- multiple statements in task body
    bif.consumer.send(8'hAB);
    `checkh(bif.data, 8'hAB);
    `checkh(bif.result, 8'hAC);

    // Test 2: send again with different value
    bif.consumer.send(8'h42);
    `checkh(bif.data, 8'h42);
    `checkh(bif.result, 8'h43);

    // Test 3: accumulate -- multiple statements + two arguments
    bif.consumer.accumulate(8'h10, 8'h20);
    `checkh(bif.data, 8'h10);
    `checkh(bif.result, 8'h30);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
