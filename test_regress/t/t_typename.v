// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


`define printtype(mytype, expec) $write({"\"", $typename(mytype), "\" ==? \"", expec, "\"\n"});

// Copied from 20.6.1 Type name function in IEEE 1800-2017
// source code // $typename would return
typedef bit node; // "bit"
node [2:0] X; // "bit [2:0]"
int signed Y; // "int"

package A;
   enum {A,B,C=99} X; // "enum{A=32'sd0,B=32'sd1,C=32'sd99}A::e$1"
   typedef bit [9:1'b1] word; // "A::bit[9:1]"
endpackage : A

import A::*;

// moved into t
// module top;
//    typedef struct {node A,B;} AB_t;
//    AB_t AB[10]; // "struct{bit A;bit B;}top.AB_t$[0:9]"
// endmodule

module t(/*AUTOARG*/);

   real r;
   logic l;
   typedef bit mybit_t;
   mybit_t [2:0] bitp20;
   mybit_t bitu32 [3:2];
   mybit_t bitu31 [3:1][4:5];
   string assoc[longint];
   int q[$];
   int q3[$:3];
   bit dyn[] = '{0, 0};

   class Cls;
      int m_c;
   endclass

   typedef union {node A,B;} UAB_t;

   // From LRM
   typedef struct {node A,B;} AB_t;
   AB_t AB[10]; // "struct{bit A;bit B;}top.AB_t$[0:9]"

   initial begin
      // $write({$typename(real), "\n"});
      `printtype(real, "real");
      `printtype(bit, "bit");
      `printtype(int, "int");
      `printtype(logic, "logic");
      `printtype(string, "string");
      `printtype(r, "real");
      `printtype(l, "logic");
      `printtype(mybit_t, "bit");
      `printtype(bitp20, "bit[2:0]");
      `printtype(bitu32, "bit$[3:2]");
      `printtype(bitu31, "bit$[3:1][4:5]");

      $write("\n");
      // from LRM
      `printtype(node, "bit");
      `printtype(X, "bit[2:0]");
      `printtype(Y, "int");

      `printtype(A::word, "bit[9:1]");
      `printtype(assoc, "string$[longint]");
      `printtype(q, "int$[$]");
      `printtype(q3, "int$[$:3]");  // Some omit :3 - need it so != unbounded
      `printtype(dyn, "bit$[]");

      $display;

      `printtype(A::X, "enum{A=32'sd0,B=32'sd1,C=32'sd99}A::<unspecified>");  // Some have just "enum <typename>"

      `printtype(AB_t, "struct{bit A;bit B;}<some_have_typename>");

      `printtype(AB, "struct{bit A;bit B;}top.AB_t$[0:9]");
      `printtype(UAB_t, "union{bit A;bit B;}");

      `printtype(Cls, "class{}t.Cls <or class t.Cls>");

      $display;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
