// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(g,e) do if ((g) !== (e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)
// verilog_format: on

module t;
  logic var_en [0:1] /*verilator forceable*/;
  logic sig;

  initial begin
    var_en[0] = 1'b0;
    var_en[1] = 1'b0;
  end

  //verilator lint_off IEEEMAYDEPRECATE
  initial assign sig = 1'b1;
  //verilator lint_on IEEEMAYDEPRECATE

  initial begin
    #1;
    force var_en[0] = 1'b1;
    #1;
    `checkh(var_en[0], 1'b1);
    `checkh(var_en[1], 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
