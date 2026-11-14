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

interface I0 #(parameter PRMTR = 1);
endinterface

interface I1;
  I0 i0 ();
endinterface

module M1 #(parameter PRMTR = 1)(
    output int value
);
  int v0, v1;
  M0 m0a (.value(v0));
  M0 m0b (.value(v1));
  I0 i0 ();
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

// Defparam values use the parameters of the instance of the module declaring them
// (IEEE 1800-2023 23.10.1)
module M4 #(parameter PRMTR = 4);
  function automatic int f();
    return PRMTR + 100;
  endfunction
  M1 m1x (.value());
  I1 i1 ();
  I0 i0 ();
  defparam m1x.m0a.PRMTR = PRMTR;  // Not M1's PRMTR
  defparam m1x.m0b.PRMTR = f();
  defparam m1x.i0.PRMTR = PRMTR;
  defparam i1.i0.PRMTR = PRMTR;
  defparam i0.PRMTR = PRMTR;
  for (genvar i = 0; i < 2; i = i + 1) begin : gen
    localparam LOCAL = PRMTR * 10 + i;
    M1 m1y (.value());
    I0 i0 ();
    defparam m1y.m0a.PRMTR = LOCAL;
    defparam i0.PRMTR = LOCAL;
  end
endmodule

module M5;
  if (1) begin : gen
    M0 m0 (.value());
  end
endmodule

package pkg;
  localparam PKG_PRMTR = 6;
  class Cls;
    localparam CLS_PRMTR = 7;
  endclass
endpackage

// Instances outside the module declaring the defparams
module M6;
  import pkg::*;
  defparam m0up.PRMTR = PKG_PRMTR;
  defparam top.m1a.m0b.PRMTR = Cls::CLS_PRMTR;
endmodule

module top;
  int value;

  M3 m3 (.value(value));
  M4 #(.PRMTR(3)) m4 ();
  M4 m4d ();
  // Instances with equal parameters, but different defparams
  M1 #(.PRMTR(2)) m1a (.value());
  M1 #(.PRMTR(2)) m1b (.value());
  M5 m5a ();
  M5 m5b ();
  M6 m6 ();
  M0 m0up (.value());
  I0 i0 ();
  generate
    begin
      M0 m0 (.value());
      defparam i0.PRMTR = 14;  // The unnamed block is not a scope
    end
  endgenerate

  defparam m1a.m0a.PRMTR = 11;
  defparam m1b.m0a.PRMTR = 12;
  defparam m5a.gen.m0.PRMTR = 21;
  defparam m5b.gen.m0.PRMTR = 22;
  defparam m0.PRMTR = 13;

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

    `checkh(m4.m1x.m0a.PRMTR, 3);
    `checkh(m4.m1x.m0b.PRMTR, 103);
    `checkh(m4.m1x.i0.PRMTR, 3);
    `checkh(m4.i1.i0.PRMTR, 3);
    `checkh(m4.i0.PRMTR, 3);
    `checkh(m4.gen[0].m1y.m0a.PRMTR, 30);
    `checkh(m4.gen[1].m1y.m0a.PRMTR, 31);
    `checkh(m4.gen[1].i0.PRMTR, 31);
    `checkh(m4d.m1x.m0a.PRMTR, 4);
    `checkh(m4d.m1x.m0b.PRMTR, 104);
    `checkh(m4d.m1x.i0.PRMTR, 4);
    `checkh(m4d.i1.i0.PRMTR, 4);
    `checkh(m4d.i0.PRMTR, 4);
    `checkh(m4d.gen[0].m1y.m0a.PRMTR, 40);
    `checkh(m4d.gen[1].m1y.m0a.PRMTR, 41);
    `checkh(m4d.gen[1].i0.PRMTR, 41);
    `checkh(m1a.m0a.PRMTR, 11);
    `checkh(m1b.m0a.PRMTR, 12);
    `checkh(m1a.m0b.PRMTR, 7);
    `checkh(m1b.m0b.PRMTR, 1);
    `checkh(m5a.gen.m0.PRMTR, 21);
    `checkh(m5b.gen.m0.PRMTR, 22);
    `checkh(m0.PRMTR, 13);
    `checkh(i0.PRMTR, 14);
    `checkh(m0up.PRMTR, 6);

    #1;
    `checkh(value, 45);  // (2+3) * (4+5)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
