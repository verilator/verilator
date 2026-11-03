// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface ifc;
  int x;
endinterface

module holder2;
  ifc i ();
endmodule

module holder;
  holder2 h2 ();
endmodule

module sub;
  virtual ifc vif;
endmodule

module t;
  sub s ();
  holder h ();

  initial begin
    s.vif = h.h2.i;
    s.vif.x = 32'h12345678;
    `checkh(h.h2.i.x, 32'h12345678);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
