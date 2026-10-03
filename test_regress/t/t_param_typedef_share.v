// DESCRIPTION: Verilator: Verilog Test module
//
// Many parameters of one typedef that depends on another parameter. The
// typedef is resolved once for the instance, not once for each parameter.
// See issue #5890.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module m;
  parameter int N = 1;
  typedef logic [N-1:0] t0;
  typedef union packed {t0 a; t0 b;} t1;
  typedef union packed {t1 a; t1 b;} t2;
  parameter t2 P0 = 0;
  parameter t2 P1 = 0;
  parameter t2 P2 = 0;
  parameter t2 P3 = 0;
  parameter t2 P4 = 0;
  parameter t2 P5 = 0;
  parameter t2 P6 = 0;
  parameter t2 P7 = 0;
endmodule

module t;
  m #(.N(4), .P0(1), .P1(2), .P2(3), .P3(4), .P4(5), .P5(6), .P6(7), .P7(8)) i_m ();

  initial begin
    `checkd($bits(i_m.P7), 4);
    `checkd(i_m.P7, 8);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
