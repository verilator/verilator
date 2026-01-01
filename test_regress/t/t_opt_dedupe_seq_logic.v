// DESCRIPTION: Verilator: Dedupe optimization test.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// Contributed 2012 by Varun Koyyalagunta, Centaur Technology.
//
//  Test consists of the follow logic tree, which has many obvious
//  places for dedupe:
/*
                               output
                                 +
                  --------------/ \--------------
                 /                               \
                +                                 +
           ----/ \-----                      ----/ \----
          /           +                     /           +
         +           / \                   +           / \
       -/ \-        a   b                -/ \-        a   b
      /     \                           /     \
     +       +                         +       +
    / \     / \                       / \     / \
   a   b   c   d                     a   b   c   d
*/

module t(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  wire left,right;
  add add(sum,left,right,clk);
  l l(left,a,b,c,d,clk);
  r r(right,a,b,c,d,clk);
endmodule

module l(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  wire left, right;
  add add(sum,left,right,clk);
  ll ll(left,a,b,c,d,clk);
  lr lr(right,a,b,c,d,clk);
endmodule

module ll(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  wire left, right;
  add add(sum,left,right,clk);
  lll lll(left,a,b,c,d,clk);
  llr llr(right,a,b,c,d,clk);
endmodule

module lll(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  add add(sum,a,b,clk);
endmodule

module llr(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  add add(sum,c,d,clk);
endmodule

module lr(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  add add(sum,a,b,clk);
endmodule

module r(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  wire left, right;
  add add(sum,left,right,clk);
  rl rl(left,a,b,c,d,clk);
  rr rr(right,a,b,c,d,clk);
endmodule

module rr(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  add add(sum,a,b,clk);
endmodule

module rl(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  wire left, right;
  add add(sum,left,right,clk);
  rll rll(left,a,b,c,d,clk);
  rlr rlr(right,a,b,c,d,clk);
endmodule

module rll(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  add2 add(sum,a,b,clk);
endmodule

module rlr(sum,a,b,c,d,clk);
  output sum;
  input a,b,c,d,clk;
  add2 add(sum,c,d,clk);
endmodule

module add(sum,x,y,clk);
  output reg sum;
  input x,y,clk;
  reg t1,t2;
  always @(posedge clk) begin
      sum <= x + y;
  end
endmodule

module add2(sum,x,y,clk);
  output reg sum;
  input x,y,clk;
  reg t1,t2;
  always @(posedge clk) begin
      sum <= x + y;
  end
endmodule
