// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package A;  // Create JUMPBLOCK; use n++ in it
  task t(input bit early, output int m, output int n);
    n = 1;
    m = 0;
    if (early) return;
    m = n++;
  endtask
endpackage

package B;  // Create IF; use n++ in it
  int n = 1;
  int m = 0;
  task t(input bit en);
    if (en) m = n++;
  endtask
endpackage

module C;  // Like above but in a module
  bit en = 1;
  int n = 1;
  int m = 0;

  initial if (en) m = n++;
endmodule

module D;  // Like above but in the module's first statement, and again after it
  initial begin : first
    static int n = 1;
    if (n++ > 0) n = n + 1;
  end
  initial begin : second
    static int n = 0;
    if (n++ > 0) n = n + 1;
  end
endmodule

module E;  // Like above but in a generate block
  for (genvar g = 0; g < 2; g++) begin : gen
    bit en = g == 1;
    int n = 0;
    int m = 0;
    initial if (++n > g) n = n + 1;
    initial if (en && ++m > 0) m = m + 1;  // Short-circuit
  end
  if (1) begin : gen_if
    int n = 0;
    initial if (++n > 0) n = n + 1;
  end
endmodule

module t;
  C c ();
  D d ();
  E e ();

  int am, an, am2, an2;

  initial begin
    A::t(0, am, an);
    A::t(1, am2, an2);
    B::t(1);
    $finish;
  end

  final begin
    `checkd(am, 1);
    `checkd(an, 2);
    `checkd(am2, 0);
    `checkd(an2, 1);
    `checkd(B::m, 1);
    `checkd(B::n, 2);
    `checkd(c.m, 1);
    `checkd(c.n, 2);
    `checkd(d.first.n, 3);
    `checkd(d.second.n, 1);
    `checkd(e.gen[0].n, 2);
    `checkd(e.gen[1].n, 1);
    `checkd(e.gen[0].m, 0);
    `checkd(e.gen[1].m, 2);
    `checkd(e.gen_if.n, 2);
    $write("*-* All Finished *-*\n");
  end
endmodule
