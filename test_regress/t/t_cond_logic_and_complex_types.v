// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`ifdef VERILATOR
// The '$c1(1)' is there to prevent inlining of the signal by V3Gate
`define IMPURE_ONE $c(1);
`else
// Use standard $random (chances of getting 2 consecutive zeros is tiny).
`define IMPURE_ONE |($random | $random);
`endif
// verilog_format: on

module t;
  typedef logic [3:0] fixed_array_t[2];
  typedef struct {
    logic [3:0] first;
    logic [3:0] second;
  } struct_t;
  typedef struct_t struct_array_t[2];

  localparam fixed_array_t FIXED_ARRAY = 1'bx ? '{4'h5, 4'h6} : '{4'h5, 4'h7};
  localparam struct_array_t STRUCT_ARRAY = 1'bx ?
  '{'{4'h1, 4'h2}, '{4'h3, 4'h4}}
  : '{'{4'h1, 4'h2}, '{4'h3, 4'h5}};
  localparam bit STRUCT_ARR_X_FIRST = STRUCT_ARRAY[1].first === 4'hx;
  localparam bit STRUCT_ARR_X_SECOND = STRUCT_ARRAY[1].second === 4'hx;

  task foo(int q[$]);
    `checkd(q.size(), 2);
    `checkd(q.pop_front(), 1);
    `checkd(q.pop_front(), 2);
  endtask
  task bar(int q[$]);
    `checkd(q.size(), 3);
    `checkd(q.pop_front(), 5);
    `checkd(q.pop_front(), 4);
    `checkd(q.pop_front(), 3);
  endtask

  initial begin
    automatic logic c;
    automatic int a[$];
    automatic int b[$];
    `checkd(FIXED_ARRAY[0], 4'h5);
    `checkd(STRUCT_ARRAY[0].first, 4'h1);
    `checkd(STRUCT_ARRAY[0].second, 4'h2);
    `checkd(STRUCT_ARR_X_FIRST, 1'b1);
    `checkd(STRUCT_ARR_X_SECOND, 1'b1);
    c = `IMPURE_ONE;
    a.push_back(1);
    a.push_back(2);
    b.push_back(5);
    b.push_back(4);
    b.push_back(3);
    foo(c ? a : b);
    c = ~c;
    bar(c ? a : b);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
