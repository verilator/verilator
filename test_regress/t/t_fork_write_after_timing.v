// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  int x1, x2, x3, x4, x5, x6, x7;

  initial begin
    x1 = -1;
    x2 = -1;
    x3 = -1;
    x4 = -1;

    #1 t1(x1);
    t2(x2);
    t3(x3);
    t4(x4);
    `checkd(x1, 0)
    `checkd(x2, -1)
    `checkd(x3, 1)
    `checkd(x4, 2)

    #10 t1(x1);
    t2(x2);
    t3(x3);
    t4(x4);
    `checkd(x1, 1)
    `checkd(x2, -1)
    `checkd(x3, 1)
    `checkd(x4, 2)

    `checkd(x5, 3)
    `checkd(x6, 0)
    `checkd(x7, 4)

    #5 $write("*-* All Finished *-*\n");
    $finish;
  end
  always #1 t5(x5);
  always #1 t6(x6);
  always #1 t7(x7);

  task t1(output int x);
    fork
      x = #1 1;
    join_none
    if ($time < 10) begin
      `checkd(x, 0)
    end
    else begin
      `checkd(x, 1)
    end
  endtask

  task t2(inout int x);
    fork
      x = #1 2;
    join_none
    `checkd(x, -1)
  endtask

 task t3(output int x);
    if ($time < 10) begin
      `checkd(x, 0)
    end
    else begin
      `checkd(x, 1)
    end
    fork
      x = #1 1;
    join_none
    #2 `checkd(x, 1);
  endtask

  task t4(inout int x);
    if ($time < 10) begin
      `checkd(x, -1)
    end
    else begin
      `checkd(x, 2)
    end
    fork
      x = #1 2;
    join_none
    #2 `checkd(x, 2);
  endtask

  task t5(output int x);
    x <= #1 3;
  endtask

  task t6(inout int x);
    x <= #1 4;
  endtask

  task static t7(inout int x);
    int y = 0;
    x <= #1 4;
    #2 y = x;
    `checkd(x, 4)
  endtask
endmodule
