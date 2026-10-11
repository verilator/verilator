// DESCRIPTION: Verilator: Verilog Test module
//
// A specialization is named from the value as written when a parameter's type refers
// to something naming can't work out; the module copy then works out the type.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  typedef enum logic [1:0] {PA, PB, PC} pe_t;
endpackage

// The width depends on the size of a variable in the module
module m_bits;
  logic [4:0] w;
  parameter logic [$bits(w)-1:0] S = '0;
endmodule

// ... or in an interface
interface ifc_bits;
  logic [4:0] w;
  parameter logic [$bits(w)-1:0] S = '0;
endinterface

// The width depends on an item of an enum declared in the module
module m_en;
  typedef enum logic [1:0] {EA, EB, EC} e_t;
  parameter int I = int'(EC);
  parameter logic [I:0] P = '0;
endmodule

// ... or in an interface
interface ifc_en;
  typedef enum logic [1:0] {EA, EB, EC} e_t;
  parameter int I = int'(EC);
  parameter logic [I:0] P = '0;
endinterface

// The width depends on an item of a package's enum, which is worked out as usual
module m_pen #(
    parameter int I = int'(pkg::PC),
    parameter logic [I:0] P = '0
) ();
endmodule

module t;
  m_bits #(.S(5'h15)) i_bits15 ();
  m_bits #(.S(5'h0a)) i_bits0a ();
  ifc_bits #(.S(5'h15)) i_ifc15 ();
  m_en #(.P(3'd5)) i_en ();
  ifc_en #(.P(3'd5)) i_ifc_en ();
  m_pen #(.P(3'd5)) i_pen ();

  initial begin
    `checkd($bits(i_bits15.S), 5);
    `checkd(i_bits15.S, 5'h15);
    `checkd(i_bits0a.S, 5'h0a);
    `checkd(i_ifc15.S, 5'h15);
    `checkd($bits(i_en.P), 3);
    `checkd(i_en.P, 5);
    `checkd($bits(i_ifc_en.P), 3);
    `checkd(i_ifc_en.P, 5);
    `checkd($bits(i_pen.P), 3);
    `checkd(i_pen.P, 5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
