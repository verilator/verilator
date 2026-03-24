// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  int x1, x2, x3, x4;

  initial begin
    x1 = -1;
    x2 = -1;
    x3 = -1;
    x4 = -1;

    #1 t1(x1);
    t2(x2);
    t3(x3);
    t4(x4);

    #10 t1(x1);
    t2(x1);
    t3(x1);
    t4(x1);
    t5(x2);
    t6(x2);

    #5 $write("*-* All Finished *-*\n");
    $finish;
  end

  task t1(output int x);
    $display("t1 start %d", x);
    fork
      x = #1 1;
    join_none
    $display("t1 end %d", x);
  endtask

  task t2(inout int xa);
    $display("t2 start %d", xa);
    fork
      xa = #1 2;
    join_none
    $display("t2 end %d", xa);
  endtask

 task t3(output int x);
    $display("t3 start %d", x);
    fork
      x = #1 1;
    join_none
    #2 $display("t3 end %d", x);
  endtask

  task t4(inout int x);
    $display("t4 start %d", x);
    fork
      x = #1 2;
    join_none
    #2 $display("t4 end %d", x);
  endtask

  task t5(output int x);
    if (x != 0) $stop;
    x <= #1 3;
  endtask

  task t6(inout int x);
    x <= #1 4;
  endtask
endmodule
