// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef int int_arr_t[];

class Cls;
  rand int x;
  rand int_arr_t arr[];
  task body();
    int ok;
    arr = new[2];
    arr[1] = new[2];
    repeat (40) begin
      ok = this.randomize() with {x == local::arr[1][1];};
      `checkd(ok, 1);
      `checkd(x, arr[1][1]);
    end
  endtask
endclass

module t;
  Cls c;
  initial begin
    c = new;
    c.body();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
