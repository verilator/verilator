// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop;
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class obj;
endclass
class base #(
  type T1 = obj,
  type T2 = obj,
  type T3 = obj
);
  T1 t1;
  T2 t2;
  T3 t3;
endclass
module t;
  base #(
    .T2 (int),
    .T3 (logic)
  ) b;
  obj o;
  initial begin
    o = new;
    b = new;
    b.t1 = o;
    b.t2 = 32;
    b.t3 = 1;
    `checkd(b.t1, o);
    `checkd(b.t2, 32);
    `checkd(b.t3, 1);
    
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
