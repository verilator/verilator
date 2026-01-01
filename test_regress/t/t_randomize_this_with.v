// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  rand int v_rand;
  int v_norand;
  task body;
    int x;
    v_norand = 42;
    x = this.randomize() with {v_rand == 0;};
    `checkd(v_rand, 0);
    `checkd(v_norand, 42);
  endtask
endclass

module t;
  initial begin
    Cls c = new;
    c.body();
    $finish;
  end
endmodule
