// DESCRIPTION: Verilator: Verilog Test module
//
// A parameter override that uses ?: to pick between assignment patterns.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg;
  typedef struct {
    int a;
    int b;
  } pair_t;
endpackage

typedef int two_t[2];

module m #(
    parameter int N = 1,
    parameter int V[N] = '{default: 0}
) ();
endmodule

// Element type from a typedef of the module
module mt;
  parameter int N = 1;
  typedef logic [3:0] nib_t;
  parameter nib_t V[N] = '{default: 0};
endmodule

module ms #(
    parameter pkg::pair_t S = '{a: 0, b: 0}
) ();
endmodule

// Elements that are arrays
module mm #(
    parameter two_t V[1] = '{'{0, 0}}
) ();
endmodule

interface ifc #(
    parameter int N = 1,
    parameter int V[N] = '{default: 0}
);
endinterface

interface ifs #(
    parameter string V[2] = '{"", ""}
);
endinterface

class cls #(
    parameter int N = 1,
    parameter int V[N] = '{default: 0}
);
  static int count;
  static function int sum();
    int s = 0;
    for (int i = 0; i < N; ++i) s += V[i];
    return s;
  endfunction
endclass

// The condition reads a parameter that defparam sets
module w;
  parameter bit SEL = 0;
  m #(.N(2), .V(SEL ? '{1, 2} : '{3, 4})) u ();
endmodule

module t;
  parameter bit GSEL = 0;  // Set to 1 by -G
  localparam int TWO = 2;
  localparam real NEG_ZERO = -0.0;

  m #(.N(2), .V(TWO > 1 ? '{1, 2} : '{3, 4})) i_then ();
  m #(.N(3), .V(TWO > 2 ? '{1, 2, 3} : '{4, 5, 6})) i_else ();
  m #(.N(2), .V(TWO > 2 ? '{1, 2} : TWO > 1 ? '{3, 4} : '{5, 6})) i_nest ();
  m #(.N(2), .V(NEG_ZERO ? '{1, 2} : '{3, 4})) i_negz ();  // -0.0 is false
  m #(.N(TWO > 1 ? 2 : 3), .V('{1, 2})) i_size ();  // A conditional of values, as before
  mt #(.N(2), .V(TWO > 1 ? '{9, 10} : '{11, 12})) i_mt ();
  ms #(.S(TWO > 1 ? '{a: 1, b: 2} : '{a: 3, b: 4})) i_ms ();
  ifc #(.N(2), .V(TWO > 1 ? '{5, 6} : '{0, 0})) i_ifc ();
  m #(.N(2), .V(GSEL ? '{1, 2} : '{3, 4})) i_gsel ();
  w i_w ();
  defparam i_w.SEL = 1;
  // A class reference in the condition, or in the operand not taken
  ifs #(.V($typename(cls#(.N(3))) != "" ? '{"a", "b"} : '{"c", "d"})) i_ifs_cond ();
  ifs #(.V(TWO > 1 ? '{"a", "b"} : '{$typename(cls#(.N(4))), "d"})) i_ifs_else ();
  typedef cls#(.N(2), .V(TWO > 1 ? '{20, 22} : '{0, 0})) cls42_t;
  typedef cls#(.N(2), .V('{20, 22})) cls42b_t;  // The same value, so the same class
  // A ?: inside a typed pattern is an ordinary one, so is signed and sized as usual
  // verilator lint_off WIDTHEXPAND
  m #(.N(2), .V(two_t'{1 ? 4'shf : 4'h0, 1 ? 8'hff + 8'h01 : 8'h00})) i_typed ();
  mm #(.V('{two_t'{1 ? 4'shf : 4'h0, 1 ? 8'hff + 8'h01 : 8'h00}})) i_typed_nest ();
  typedef cls#(.N(2), .V(two_t'{1 ? 4'shf : 4'h0, 1 ? 8'hff + 8'h01 : 8'h00})) cls_typed_t;
  // verilator lint_on WIDTHEXPAND

  initial begin
    `checkd(i_then.V[0], 1);
    `checkd(i_then.V[1], 2);
    `checkd(i_else.V[0], 4);
    `checkd(i_else.V[2], 6);
    `checkd(i_nest.V[0], 3);
    `checkd(i_nest.V[1], 4);
    `checkd(i_negz.V[0], 3);
    `checkd($size(i_size.V), 2);
    `checkd(i_size.V[1], 2);
    `checkd($bits(i_mt.V[0]), 4);
    `checkd(i_mt.V[1], 10);
    `checkd(i_ms.S.a, 1);
    `checkd(i_ms.S.b, 2);
    `checkd(i_ifc.V[1], 6);
    `checkd(i_gsel.V[0], 1);
    `checkd(i_w.u.V[0], 1);
    `checks(i_ifs_cond.V[0], "a");
    `checks(i_ifs_else.V[1], "b");
    `checkd(cls42_t::sum(), 42);
    cls42_t::count = 5;
    `checkd(cls42b_t::count, 5);
    `checkd(cls#(.N(2), .V(TWO > 1 ? '{1, 1} : '{0, 0}))::sum(), 2);
    `checkd(i_typed.V[0], 15);
    `checkd(i_typed.V[1], 256);
    `checkd(i_typed_nest.V[0][0], 15);
    `checkd(i_typed_nest.V[0][1], 256);
    `checkd(cls_typed_t::sum(), 271);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
