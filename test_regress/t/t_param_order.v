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
class TypeParams #(
    type T1 = obj,
    type T2 = obj,
    type T3 = obj
);
  T1 t1;
  T2 t2;
  T3 t3;
endclass

class ValueParams #(
    int P1 = 1,
    int P2 = 1,
    int P3 = 1
);
  logic [P1:0] x1;
  logic [P2:0] x2;
  logic [P3:0] x3;
endclass

class Mixed #(
    type T1 = obj,
    int P1 = 1,
    type T2 = obj,
    int P2 = 1,
    type T3 = obj,
    int P3 = 1
);
  T1 t1;
  T2 t2;
  T3 t3;
  logic [P1:0] x1;
  logic [P2:0] x2;
  logic [P3:0] x3;
endclass

module t;
  TypeParams #(
      .T2(int),
      .T3(logic)
  ) t;
  obj o;

  ValueParams #(
      .P3(5),
      .P2(2)
  ) v;

  Mixed #(
      .P3(3),
      .T1(logic),
      .T3(int),
      .P2(7)
  ) m;
  initial begin
    o = new;
    t = new;
    t.t1 = o;
    t.t2 = 32;
    t.t3 = 1;
    if (t.t1 != o) $stop;
    `checkd(t.t2, 32);
    `checkd(t.t3, 1);

    v = new;
    v.x1 = 2;
    v.x2 = 5;
    v.x3 = 40;
    `checkd(v.x1, 2);
    `checkd(v.x2, 5);
    `checkd(v.x3, 40);

    m = new;
    m.t1 = 1;
    m.t2 = o;
    m.t3 = 12345;
    m.x1 = 0;
    m.x2 = 250;
    m.x3 = 15;
    `checkd(m.t1, 1);
    if (m.t2 != o) $stop;
    `checkd(m.t3, 12345);
    `checkd(m.x1, 0);
    `checkd(m.x2, 250);
    `checkd(m.x3, 15);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
