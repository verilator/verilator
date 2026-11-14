// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ifc;
  logic in;
  logic out;
endinterface

module a (
    in,
    out,
    ifc_if
);
  input in;
  output out;
  assign out = !in;
  ifc ifc_if;
  assign ifc_if.out = ifc_if.in;
  sub sub ();
  initial $display("In '%m'");
endmodule

module b (
    in,
    out,
    ifc_if
);
  input in;
  output out;
  assign out = in;
  ifc ifc_if;
  assign ifc_if.out = !ifc_if.in;
  sub sub ();
  initial $display("In '%m'");
endmodule

module c (
    uniq_in,
    uniq_out,
    uniq_ifc_if
);
  input uniq_in;
  output uniq_out;
  assign uniq_out = !uniq_in;
  ifc uniq_ifc_if;
  assign uniq_ifc_if.out = !uniq_ifc_if.in;
  sub sub ();
  initial $display("In '%m'");
endmodule

module sub;
  initial $display("In '%m'");
endmodule
