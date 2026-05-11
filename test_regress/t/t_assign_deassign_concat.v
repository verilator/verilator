// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  reg a;
  reg b;
  reg c;
  reg d;
  reg control;
  reg clock = 0;

  always @(posedge clock) {a, b, c, d} = 4'h3;

  always @(control)
    if (control) begin
      assign {a, b, c, d} = 4'h2;
    end
    else begin
      deassign {a, b, c, d};
    end

  always begin
    #2;
    clock = ~clock;
  end

  initial begin
    #3;
    `checkh({a, b, c, d}, 4'h3)
    #2;
    control = 1;
    #1;
    `checkh({a, b, c, d}, 4'h2)
    #3;
    control = 0;
    #2;
    `checkh({a, b, c, d}, 4'h3)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
