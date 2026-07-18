// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class C;
  typedef logic [1:0] T;
  class nst;
    typedef logic [2:0] S;
  endclass
endclass: C

class D;
  typedef logic [3:0] T;
  class nst;
    typedef logic [4:0] S;
  endclass
endclass: D

class P#(type C);
  localparam type C1_t = C::T;
  parameter type C2_t = C::nst::S;
  C1_t x = '1;
  C2_t y = '1;
endclass : P

module t();
  P#(C) PC_data = new();
  P#(D) PD_data = new();
  initial begin
    `checkd($bits(PC_data.x), 2);
    `checkd($bits(PC_data.y), 3);
    `checkd($bits(PD_data.x), 4);
    `checkd($bits(PD_data.y), 5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
