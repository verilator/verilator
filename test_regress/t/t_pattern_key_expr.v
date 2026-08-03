// DESCRIPTION: Verilator: Assignment pattern keys may be constant expressions
//
// IEEE 1800-2017 A.6.7.1 (Syntax 10-5):
//   array_pattern_key ::= constant_expression | assignment_pattern_key
//   structure_pattern_key ::= member_identifier | assignment_pattern_key
//   assignment_pattern_key ::= simple_type | default
// so an array key is any constant expression, while a structure key is only a
// member name or a type.
//
// Real-indexed associative arrays below are a Verilator extension beyond
// IEEE 1800-2017 7.8.5; they are covered here to keep pre-existing behavior.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%g exp=%g\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package Pkg;
  localparam int PKG_KEY = 5;
  typedef int pkg_int_t;
endpackage

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  localparam int P = 2;

  typedef enum int {
    E0,
    E1,
    E2
  } e_t;

  typedef struct packed {
    int a;
    int b;
  } pair_t;

  const string aa[longint] = '{1: "A", 1 << 10: "B", 1 << 20: "C", 1 << 30: "D"};

  // Unpacked array, various constant-expression keys
  int unpk[9] = '{0: 10, 1 + 1: 12, P * 3: 16, 7 - 4: 13, 4'd8: 18, default: 99};

  // Packed array, constant-expression keys
  logic [6:0] pkd = '{0: 1'b1, 1 + 2: 1'b1, 3 * 2: 1'b1, default: 1'b0};

  // Negative and descending-range keys
  int neg[-4:4] = '{-4 + 1: 21, 0 - 2: 22, -P * 2: 23, default: 0};

  // Parenthesised, concatenated and unary-operator keys
  int ops[8] = '{(P + 1) * 2: 24, {2'b1, 1'b1} : 25, ~(-2): 26, default: 0};

  // Parameter and package-scoped parameter keys, still supported
  int prm[8] = '{P: 31, Pkg::PKG_KEY: 33, default: 0};

  // Enum item keys, and expressions over them
  int enm[4] = '{E1: 41, int'(E2) + 1: 43, default: 0};

  // Structure member-name keys, still supported
  pair_t strct = '{a: 51, b: 52};

  // Structure data-type keys, still supported.  IEEE 1800-2017 A.2.2.1
  // simple_type includes ps_type_identifier, which A.9.3 allows to carry a
  // package_scope, so both forms below are legal keys.
  pair_t strct_dt = '{int : 53};
  pair_t strct_pkg_dt = '{Pkg::pkg_int_t: 54};

  // String keys, including an expression over them
  int smap[string] = '{"a": 61, {"b", "c"} : 62};

  // Real keys.  A real associative array index is a Verilator extension;
  // IEEE 1800-2017 7.8.5 makes real an illegal index type.  Verilator has
  // always accepted it, so keep it working.  The negated key is newly
  // accepted, as the old grammar had no '-' yaFLOATNUM alternative.
  real rmap[real] = '{1.5: 1.25, 1.5 + 1.0: 2.25, -1.5: 3.25};

  // Nested pattern as the value of an expression key
  int nest[2][3] = '{0: '{71, 72, 73}, 1 << 0: '{74, 75, 76}};

  // A ternary in a positional element must still parse as one expression
  int tern[1] = '{P == 2 ? 81 : 82};

  int cyc = 0;
  int dyn[4];

  initial begin
    `checks(aa[1], "A")
    `checks(aa[1024], "B")
    `checks(aa[1048576], "C")
    `checks(aa[1073741824], "D")
    `checkd(aa.size(), 4)

    `checkd(unpk[0], 10)
    `checkd(unpk[1], 99)
    `checkd(unpk[2], 12)
    `checkd(unpk[3], 13)
    `checkd(unpk[6], 16)
    `checkd(unpk[8], 18)

    `checkd(pkd, 7'b1001001)

    `checkd(neg[-3], 21)
    `checkd(neg[-2], 22)
    `checkd(neg[-4], 23)
    `checkd(neg[0], 0)

    `checkd(ops[6], 24)
    `checkd(ops[3], 25)
    `checkd(ops[1], 26)
    `checkd(ops[0], 0)

    `checkd(prm[2], 31)
    `checkd(prm[5], 33)
    `checkd(prm[0], 0)

    `checkd(enm[1], 41)
    `checkd(enm[3], 43)
    `checkd(enm[0], 0)

    `checkd(strct.a, 51)
    `checkd(strct.b, 52)
    `checkd(strct_dt.a, 53)
    `checkd(strct_dt.b, 53)
    `checkd(strct_pkg_dt.a, 54)
    `checkd(strct_pkg_dt.b, 54)

    `checkd(smap["a"], 61)
    `checkd(smap["bc"], 62)
    `checkr(rmap[1.5], 1.25)
    `checkr(rmap[2.5], 2.25)
    `checkr(rmap[-1.5], 3.25)

    `checkd(nest[0][0], 71)
    `checkd(nest[0][2], 73)
    `checkd(nest[1][0], 74)
    `checkd(nest[1][2], 76)

    `checkd(tern[0], 81)
  end

  // Runtime-varying values under constant-expression keys
  always @(posedge clk) begin
    dyn <= '{1 << 1: cyc, 3 - 3: cyc + 100, default: cyc + 200};
    if (cyc > 0) begin
      `checkd(dyn[0], cyc + 99)
      `checkd(dyn[1], cyc + 199)
      `checkd(dyn[2], cyc - 1)
      `checkd(dyn[3], cyc + 199)
    end
    cyc <= cyc + 1;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
