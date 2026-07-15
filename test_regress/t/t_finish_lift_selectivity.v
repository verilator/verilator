// DESCRIPTION: Verilator: Finish-sensitive lifting ignores unrelated sibling statements
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

`define NEST_1(STMT) \
  if (calls >= 0) begin \
    STMT \
  end
`define NEST_2(STMT) `NEST_1(`NEST_1(STMT))
`define NEST_4(STMT) `NEST_2(`NEST_2(STMT))
`define NEST_8(STMT) `NEST_4(`NEST_4(STMT))
`define NEST_16(STMT) `NEST_8(`NEST_8(STMT))
`define NEST_32(STMT) `NEST_16(`NEST_16(STMT))
`define NEST_64(STMT) `NEST_32(`NEST_32(STMT))
`define NEST_128(STMT) `NEST_64(`NEST_64(STMT))

`define NEST_EXPR_1(EXPR) (expr_acc += (EXPR))
`define NEST_EXPR_2(EXPR) `NEST_EXPR_1(`NEST_EXPR_1(EXPR))
`define NEST_EXPR_4(EXPR) `NEST_EXPR_2(`NEST_EXPR_2(EXPR))
`define NEST_EXPR_8(EXPR) `NEST_EXPR_4(`NEST_EXPR_4(EXPR))

`define NEST_WITH_1(EXPR) callback_values.sum with (item + (EXPR))
`define NEST_WITH_2(EXPR) `NEST_WITH_1(`NEST_WITH_1(EXPR))
`define NEST_WITH_4(EXPR) `NEST_WITH_2(`NEST_WITH_2(EXPR))
`define NEST_WITH_8(EXPR) `NEST_WITH_4(`NEST_WITH_4(EXPR))
`define NEST_WITH_16(EXPR) `NEST_WITH_8(`NEST_WITH_8(EXPR))
// verilog_format: on

module t;
  int calls;
  int callback_values[$] = '{1};

  function automatic int ordinary(input int value);
    ++calls;
    return value;
  endfunction

  function automatic int may_finish(input int value);
    calls += 10;
    if (value != 0) $finish;
    return value;
  endfunction

  initial begin
    int callback_result;
    int result;
    int expr_acc;
    result = ordinary(1) + 1;
    `NEST_128(result = may_finish(0) + 2;)
    expr_acc = 0;
    expr_acc = `NEST_EXPR_8(0);
    callback_result = `NEST_WITH_16(may_finish(0));
    `checkd(calls, 21);
    `checkd(result, 2);
    `checkd(expr_acc, 0);
    `checkd(callback_result, 16);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
