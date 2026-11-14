// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`timescale 1ns / 1ps

interface ifc;
  int d = 0;
  int w = 0;
endinterface

class Cls;
  int x = 0;
endclass

module t;
  // An 'always @*' with timing controls that reads a member of a virtual interface or of a
  // class object waits on that member, not only on its handle
  ifc i_ifc ();
  virtual ifc vif = i_ifc;
  Cls obj = new;
  int y_vif = 0;
  int y_cls = 0;
  always @* y_vif <= #1 vif.d;
  always @* y_cls <= #1 obj.x;
  // Writing a member: woken by what the statement reads, not by the handle
  int a = 0;
  always @* vif.w <= #1 a;

  initial begin
    #10 i_ifc.d = 5;
    obj.x = 6;
    a = 3;
    #2;
    `checkd(y_vif, 5);
    `checkd(y_cls, 6);
    `checkd(i_ifc.w, 3);
    a = 4;
    i_ifc.d = 7;
    obj = new;  // A new object, with its own member value
    obj.x = 9;
    #2;
    `checkd(y_vif, 7);
    `checkd(y_cls, 9);
    `checkd(i_ifc.w, 4);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
