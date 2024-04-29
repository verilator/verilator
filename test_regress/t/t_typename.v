// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


`define printtype(mytype) $write({$typename(mytype), "\n"});

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


   // from LRM
   typedef struct {node A,B;} AB_t;
   AB_t AB[10]; // "struct{bit A;bit B;}top.AB_t$[0:9]"

   initial begin
      // $write({$typename(real), "\n"});
      `printtype(real);
      `printtype(int);
      `printtype(int);
      `printtype(logic);
      `printtype(string);
      `printtype(r);
      `printtype(l);
      `printtype(mybit_t);
      `printtype(bitp20);
      `printtype(bitu32);
      `printtype(bitu31);

      $write("\n");
      // from LRM
      `printtype(node); // bit
      `printtype(X); // bit [2:0]
      `printtype(Y); // int
      `printtype(A::X); // enum{A=32'sd0,B=32'sd1,C=32'sd99}A::e$1
      `printtype(A::word); // A::bit[9:1]
      `printtype(AB); // struct{bit A;bit B;}top.AB_t$[0:9]

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
