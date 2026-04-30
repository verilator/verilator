// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0
// verilog_format: off

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

// verilog_format: on

typedef byte unsigned uint8_t;

class D;
  rand uint8_t x;
endclass

class test;

  D d;

  task run_phase;
    process p;
    uint8_t result;
    string randstate;

    // Pass 1: seed process, create object, randomize, record result
    p = process::self();
    p.srandom(100);
    d = new;
    // Save randstate AFTER d=new (d=new advances process RNG per IEEE 18.14.1)
    randstate = p.get_randstate();
    `checkd(d.randomize(), 1);
    result = d.x;

    // Pass 2: same seed -> same sequence -> same result
    p.srandom(100);
    d = new;
    `checks(p.get_randstate(), randstate);
    `checkd(d.randomize(), 1);
    `checkd(d.x, result);

    // Pass 3: same seed, with intervening task call -> same result
    p.srandom(100);
    other_task();
    d = new;
    `checks(p.get_randstate(), randstate);
    `checkd(d.randomize(), 1);
    `checkd(d.x, result);
  endtask

  task other_task;
    // verilator no_inline_task
    $display("Other task");
  endtask

endclass

module t;
  initial begin
    test c;
    c = new;
    c.run_phase();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
