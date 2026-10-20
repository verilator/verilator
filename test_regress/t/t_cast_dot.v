// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  typedef enum {A, B, C} e_t;
  typedef struct packed {
    int x;
    int y;
  } s_t;

  int i = 1;

  initial begin
    // Method call on a cast
    `checks(e_t'(i).name(), "B");
    `checks(e_t'(i).next().name(), "C");
    // Member select on a cast
    `checkh(s_t'({32'd5, 32'd7}).x, 5);
    `checkh(s_t'({32'd5, 32'd7}).y, 7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
