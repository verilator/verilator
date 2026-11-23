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
  typedef struct {
    string s;
    logic [7:0] v;
  } S;

  // Not trivially constructible, so its force signals are nested in separate structs
  S x  /*verilator forceable*/  /*verilator public_flat_rw*/;
  S forcedVal;

  initial begin
    x.s = "keep";
    x.v = 8'h12;
    forcedVal.s = "forced";
    forcedVal.v = 8'h56;
    #1;
    `checks(x.s, "keep");
    `checkh(x.v, 8'h12);
    force x = forcedVal;
    #1;
    `checks(x.s, "forced");
    `checkh(x.v, 8'h56);
    x.s = "ignored";
    #1;
    `checks(x.s, "forced");
    release x;
    x.s = "released";
    #1;
    `checks(x.s, "released");
    `checkh(x.v, 8'h56);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
