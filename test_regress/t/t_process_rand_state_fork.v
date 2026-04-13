// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0
// verilog_format: off

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

// verilog_format: on

typedef byte unsigned uint8_t;

class D;
  rand uint8_t x;
endclass

module t;
  uint8_t result_a;
  uint8_t result_b;

  initial begin
    // Test that two fork branches with same seed produce same results
    // (each branch gets its own process with independent RNG)
    fork
      begin
        process p;
        D d;
        p = process::self();
        p.srandom(42);
        d = new;
        `checkd(d.randomize(), 1);
        result_a = d.x;
      end
      begin
        process p;
        D d;
        p = process::self();
        p.srandom(42);
        d = new;
        `checkd(d.randomize(), 1);
        result_b = d.x;
      end
    join

    // Both branches seeded identically -> same result
    `checkd(result_a, result_b);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
