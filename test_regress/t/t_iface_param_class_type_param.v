// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Test that parameterized class typedefs work as interface type parameters
// when the class itself has type parameters.
// See issue #7000

// Class with single type parameter
class C #(parameter type T = logic);
  typedef struct packed { T data; } td_t;
endclass

// Class with multiple type parameters and multiple typedefs
class multi_param #(parameter type ADDR_T = logic, parameter type DATA_T = logic);
  typedef struct packed { ADDR_T addr; } addr_td_t;
  typedef struct packed { DATA_T data; } data_td_t;
endclass

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Leaf interface: holds a value of parameterized type
interface l0 #(type P = logic);
  P p;
endinterface

// 1-level nesting: wraps l0 with a class typedef parameter
interface l1 #(parameter type X = C#(logic));
  l0 #(.P(X::td_t)) sub();
endinterface

// 2-level nesting: forwards type param through l1 to l0
interface l2 #(parameter type X = C#(logic));
  l1 #(.X(X)) sub();
endinterface

// Multi-param leaf: holds two values of different parameterized types
interface multi_l0 #(type P = logic, type Q = logic);
  P p;
  Q q;
endinterface

// Multi-param nesting: accesses different typedefs from same class
interface multi_l1 #(
  parameter type CFG = multi_param#(logic, logic)
);
  multi_l0 #(.P(CFG::addr_td_t), .Q(CFG::data_td_t)) sub();
endinterface

module t;
  // Test 1-level nesting with different parameterizations
  l1 #(.X(C#(logic[7:0]))) l1_i1();
  l1 #(.X(C#(logic[15:0]))) l1_i2();
  // Test default type parameter (C#(logic) -> td_t is struct packed { logic data; })
  l1 l1_default();

  // Test 2-level nesting - type parameter passed through multiple levels
  l2 #(.X(C#(logic[31:0]))) l2_i();

  // Test multiple type params - different parameterizations accessing multiple typedefs
  multi_l1 #(.CFG(multi_param#(logic[7:0], logic[31:0]))) ml1_i1();
  multi_l1 #(.CFG(multi_param#(logic[15:0], logic[63:0]))) ml1_i2();

  initial begin
    // 1-level nesting
    `checkd($bits(l1_i1.sub.p), 8);
    `checkd($bits(l1_i2.sub.p), 16);
    `checkd($bits(l1_default.sub.p), 1);  // default C#(logic) -> 1-bit

    // 2-level nesting
    `checkd($bits(l2_i.sub.sub.p), 32);

    // Multiple type params passed to sub-interface - two different typedefs
    `checkd($bits(ml1_i1.sub.p), 8);   // addr_td_t from ADDR_T=logic[7:0]
    `checkd($bits(ml1_i1.sub.q), 32);  // data_td_t from DATA_T=logic[31:0]
    `checkd($bits(ml1_i2.sub.p), 16);  // addr_td_t from ADDR_T=logic[15:0]
    `checkd($bits(ml1_i2.sub.q), 64);  // data_td_t from DATA_T=logic[63:0]

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
