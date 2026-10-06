// DESCRIPTION: Verilator: Verilog Test module
//
// A parameter override that is a conditional with assignment pattern operands
// takes the operand its constant condition selects, typed by the parameter.
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

// A class specialization from a typed pattern with a parameter member, in two instances
module w #(
    parameter int X = 1
) ();
  typedef int arr_t[2];
  typedef cls#(.N(2), .V(X > 0 ? arr_t'{X, 2} : '{0, 0})) c_t;
  function automatic int sum();
    return c_t::sum();
  endfunction
endmodule

module t;
  localparam int TWO = 2;
  localparam int ARR[2] = '{7, 8};
  localparam pkg::pair_t PAIR = '{a: 7, b: 8};
  localparam real NEG_ZERO = -0.0;
  typedef int arr2_t[2];

  m #(.N(2), .V(TWO > 1 ? '{1, 2} : '{3, 4})) i_then ();
  m #(.N(3), .V(TWO > 2 ? '{1, 2, 3} : '{4, 5, 6})) i_else ();
  m #(.N(2), .V(TWO > 2 ? '{1, 2} : TWO > 1 ? '{3, 4} : '{5, 6})) i_nest ();
  m #(.N(2), .V(TWO > 1 ? ARR : '{5, 6})) i_arr ();  // A parameter selected over a pattern
  m #(.N(2), .V(TWO > 2 ? ARR : '{5, 6})) i_pat ();  // A pattern selected over a parameter
  m #(.N(2), .V(TWO > 1 ? arr2_t'{9, 8} : '{0, 0})) i_typed ();  // A typed unpacked pattern
  m #(.N(TWO > 1 ? 2 : 3), .V('{1, 2})) i_size ();  // A conditional of values, as before
  mt #(.N(2), .V(TWO > 1 ? '{9, 10} : '{11, 12})) i_mt ();
  ms #(.S(TWO > 1 ? '{a: 1, b: 2} : '{a: 3, b: 4})) i_ms ();
  ms #(.S(TWO > 1 ? PAIR : '{a: 3, b: 4})) i_msp ();  // An unpacked struct parameter
  ifc #(.N(2), .V(TWO > 1 ? '{5, 6} : '{0, 0})) i_ifc ();
  // A condition converts to a bit as in any conditional, so -0.0 is false
  m #(.N(2), .V(NEG_ZERO ? '{1, 2} : '{3, 4})) i_negz ();
  // A vector with a bit set is true, even with another bit unknown
  // verilator lint_off WIDTHTRUNC
  m #(.N(2), .V(2'b1x ? '{1, 2} : '{3, 4})) i_known ();
  // verilator lint_on WIDTHTRUNC
  // A class reference in the condition, or in the operand not taken, with a conditional pin
  ifs #(.V($typename(cls#(.N(3))) != "" ? '{"a", "b"} : '{"c", "d"})) i_ifs_cond ();
  ifs #(.V(TWO > 1 ? '{"a", "b"} : '{$typename(cls#(.N(4))), "d"})) i_ifs_else ();
  ifs #(.V(TWO > 2 ? '{$typename(cls#(.V(TWO > 1 ? '{1} : '{2}))), ""} : '{"c", ""})) i_ifs_then ();
  typedef cls#(.N(2), .V(TWO > 1 ? '{20, 22} : '{0, 0})) cls42_t;
  typedef cls#(.N(2), .V('{20, 22})) cls42b_t;  // The same value, so the same class
  typedef cls#(.N(2), .V(TWO > 1 ? arr2_t'{TWO + 1, TWO * 2} : '{0, 0})) cls7_t;
  w #(.X(3)) i_w3 ();
  w #(.X(7)) i_w7 ();

  initial begin
    `checkd(i_then.V[0], 1);
    `checkd(i_then.V[1], 2);
    `checkd(i_else.V[0], 4);
    `checkd(i_else.V[2], 6);
    `checkd(i_nest.V[0], 3);
    `checkd(i_nest.V[1], 4);
    `checkd(i_arr.V[0], 7);
    `checkd(i_arr.V[1], 8);
    `checkd(i_pat.V[0], 5);
    `checkd(i_pat.V[1], 6);
    `checkd(i_typed.V[0], 9);
    `checkd(i_typed.V[1], 8);
    `checkd($size(i_size.V), 2);
    `checkd(i_size.V[1], 2);
    `checkd($bits(i_mt.V[0]), 4);
    `checkd(i_mt.V[0], 9);
    `checkd(i_mt.V[1], 10);
    `checkd(i_ms.S.a, 1);
    `checkd(i_ms.S.b, 2);
    `checkd(i_msp.S.a, 7);
    `checkd(i_msp.S.b, 8);
    `checkd(i_ifc.V[1], 6);
    `checkd(i_negz.V[0], 3);
    `checkd(i_negz.V[1], 4);
    `checkd(i_known.V[0], 1);
    `checkd(i_known.V[1], 2);
    `checks(i_ifs_cond.V[0], "a");
    `checks(i_ifs_else.V[1], "b");
    `checks(i_ifs_then.V[0], "c");
    `checkd(cls42_t::sum(), 42);
    cls42_t::count = 5;
    `checkd(cls42b_t::count, 5);
    `checkd(cls#(.N(2), .V(TWO > 1 ? '{1, 1} : '{0, 0}))::sum(), 2);
    `checkd(cls7_t::sum(), 7);
    `checkd(i_w3.sum(), 5);
    `checkd(i_w7.sum(), 9);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
