// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  // test static argument
  task t1(output int x);
    x = #1 x + 1;
  endtask

  // test concurrent executions of static tasks
  int expected;
  task t2(inout int x);
    #5 `checkd(x, expected);
  endtask
    

  task factorial1 (input [31:0] x, output [31:0] out);
    if (x >= 2) begin
      factorial1 (x - 1, out);
      out = out * x;
    end
    else
      out = 1;
  endtask

  function int factorial2 (input int x);
    if (x >= 2)
      factorial2 = factorial2(x - 1) * x;
    else
      factorial2 = 1;
  endfunction
  
  int result;
  initial begin
    // t1
    result = 0;
    t1(result);
    `checkd(result, 1);
    t1(result);
    `checkd(result, 2);
    t1(result);
    `checkd(result, 3);
    t1(result);
    `checkd(result, 4);
    
    factorial1(1, result);
    `checkd(result, 1);
    factorial1(3, result);
    `checkd(result, 6);
    factorial1(5, result);
    `checkd(result, 120);
    
    `checkd(factorial2(1), 1);
    `checkd(factorial2(3), 6);
    `checkd(factorial2(5), 120);

    // t2
    expected = 3;
    fork
      begin
        static int x1 = 1;
        t2(x1);
        `checkd(x1, 3);
      end
    join_none
    #2
    fork
      begin
        static int x2 = 3;
        t2(x2);
        `checkd(x2, 3);
      end
    join_none

    #10
    expected = 10;
    fork
      begin
        static int x3 = 99;
        t2(x3);
        `checkd(x3, 10);
      end
    join_none
    #1
    fork
      begin
        static int x4 = 123;
        t2(x4);
        `checkd(x4, 10);
      end
    join_none
    #1
    fork
      begin
        static int x5 = 10;
        t2(x5);
        `checkd(x5, 10);
      end
    join_none


    #10
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
