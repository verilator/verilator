// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module M0 #(parameter PRMTR = 1) (
    output int value
);
  assign value = PRMTR;
endmodule

module M1 #(parameter PRMTR = 1)(
    output int value
);
  int v0, v1;
  M0 m0a (.value(v0));
  M0 m0b (.value(v1));
  assign value = v0 + v1;
endmodule

module M2 #(parameter PRMTR = 1)(
    output int value
);
  M1 m1 (.value(value));
endmodule

module M3 #(parameter PRMTR = 1)(
    output int value
);
  int v0, v1;
  M2 m2a (.value(v0));
  M2 m2b (.value(v1));
  assign value = v0 * v1;
endmodule

module top;
  int value;

  M3 m3 (.value(value));

  defparam m3.m2a.m1.m0a.PRMTR = 2;
  defparam m3.m2a.m1.m0b.PRMTR = 3;
  defparam m3.m2b.m1.m0a.PRMTR = 4;
  defparam m3.m2b.m1.m0b.PRMTR = 5;

  defparam m3.m2a.m1.PRMTR = 6;
  defparam m3.m2b.m1.PRMTR = 7;

  defparam m3.m2a.PRMTR = 8;
  defparam m3.m2b.PRMTR = 9;

  defparam m3.PRMTR = 10;

  initial begin
    `checkh(m3.m2a.m1.m0a.PRMTR, 2);
    `checkh(m3.m2a.m1.m0b.PRMTR, 3);
    `checkh(m3.m2b.m1.m0a.PRMTR, 4);
    `checkh(m3.m2b.m1.m0b.PRMTR, 5);

    `checkh(m3.m2a.m1.PRMTR, 6);
    `checkh(m3.m2b.m1.PRMTR, 7);

    `checkh(m3.m2a.PRMTR, 8);
    `checkh(m3.m2b.PRMTR, 9);

    `checkh(m3.PRMTR, 10);

    #1;
    `checkh(value, 45);  // (2+3) * (4+5)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
