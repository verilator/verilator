// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(args) $write args
`else
 `define WRITE_VERBOSE(args)
`endif

`define STRINGIFY(text) `"text`"

//========================================================================
// Various expression tests. The macro generates a module with the desired
// input and tested expression.
//
`define EXPR_TEST(name, test_edges, inputs, expr) \
module t_``name inputs; \
   logic[$bits(expr)-1:0] last = 0; \
   always @(expr) begin \
       if ($bits(expr) > 1) begin \
           `WRITE_VERBOSE(("[%0t] %s [changed] %s=%0x, last=%0x\n", $time, `STRINGIFY(name), `STRINGIFY(expr), expr, last)); \
       end \
       if ($time > 0 && (expr) == last) $stop; \
       last <= expr; \
   end \
   generate if (test_edges) begin \
       always @(posedge expr) begin \
           `WRITE_VERBOSE(("[%0t] %s [posedge] %s=%0x, last=%0x\n", $time, `STRINGIFY(name), `STRINGIFY(expr), expr, last)); \
           if ($time > 0 && ({1'b0, ~(expr)}[0] || last[0])) $stop; \
       end \
       always @(negedge expr) begin \
           `WRITE_VERBOSE(("[%0t] %s [negedge] %s=%0x, last=%0x\n", $time, `STRINGIFY(name), `STRINGIFY(expr), expr, last)); \
           if ($time > 0 && ({1'b0, expr}[0] || ~last[0])) $stop; \
       end \
   end endgenerate \
endmodule

`EXPR_TEST(xor, 1, (input a, b), b^a)
`EXPR_TEST(nand, 1, (input a, b, c), ~(c&b&a))
`EXPR_TEST(concat1, 1, (input a, b, c), {{a, b},c,a,{2{a,b,c}}})
`EXPR_TEST(reduce, 1, (input[3:0] v), v[0]^v[1]^v[2]^v[3])
`EXPR_TEST(concat2, 1, (input[3:0] v), {{v[0]|v[1]},v[1]|v[2],{4{v[2]|v[3]}}})
`EXPR_TEST(add, 0, (input int i, j), i+j)
`EXPR_TEST(lt, 1, (input int i, j), i<j)
`EXPR_TEST(array, 0, (input int t[5]), t[4])
`EXPR_TEST(array_complex, 0, (input int t[5], int cyc), t[cyc / 4])
`EXPR_TEST(queue, 0, (input int q[$]), q[0])
`EXPR_TEST(queue_mul, 0, (input int q[$], int i), q[0]*i)

`ifdef UNSUP
function int id(int x); return x; endfunction
`EXPR_TEST(func, 0, (input int cyc), id(cyc))
`endif

//========================================================================
// Class tests (special case as V3Width doesn't always properly handle
// out-of-module classes
//
`ifndef NO_CLASS
`define CLASS_TEST(name, expr) \
module t_``name(input int k); \
   class Cls; \
       int k; \
       function int get_k(); return k; endfunction \
   endclass \
   Cls obj = new; \
   assign obj.k = k; \
   int last = 0; \
   always @(expr) begin \
       `WRITE_VERBOSE(("[%0t] %s [changed] %s=%0x, last=%0x\n", $time, `STRINGIFY(name), `STRINGIFY(expr), expr, last)); \
       if ($time > 0 && expr == last) $stop; \
       last <= expr; \
   end \
endmodule

`CLASS_TEST(class, obj.k)

`ifdef UNSUP
`CLASS_TEST(method, obj.get_k())
`endif
`endif

//========================================================================
// $c test has to be written out explicitly as the STRINGIFY macro can't handle it
//
module t_cstmt;
   logic last = 0;
   always @($c("vlSelf->clk")) begin
       if ($time > 0 && logic'($c("vlSelf->clk")) == last) $stop;
       last <= logic'($c("vlSelf->clk"));
   end
   always @(posedge $c("vlSelf->clk")) begin
       `WRITE_VERBOSE(("[%0t] cstmt [posedge] $c(\"vlSelf->clk\")=%0b, last=%b\n", $time, $c("vlSelf->clk"), last));
       if ($time > 0 && (~logic'($c("vlSelf->clk")) || last)) $stop;
   end
   always @(negedge $c("vlSelf->clk")) begin
       `WRITE_VERBOSE(("[%0t] cstmt [negedge] $c(\"vlSelf->clk\")=%0b, last=%b\n", $time, $c("vlSelf->clk"), last));
       if ($time > 0 && (logic'($c("vlSelf->clk")) || !last)) $stop;
   end
endmodule

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic a = 0, b = 0, c = 0;
   t_xor u_xor(.*);
   t_nand u_nand(.*);
   t_concat1 u_concat1(.*);

   logic[3:0] v = '0;
   t_reduce u_reduce(.*);
   t_concat2 u_concat2(.*);

   int i = 0, j = 0;
   t_add u_add(.*);
   t_lt u_lt(.*);

   int t[5] = {0, 1, 2, 3, 4};
   t_array u_array(.*);
   t_array_complex u_array_complex(.*);

   int q[$];
   t_queue u_queue(.*);
   t_queue_mul u_queue_mul(.*);

`ifdef UNSUP
   t_func u_func(.*);
`endif

   int k;
   assign k = i + j;
   `ifndef NO_CLASS
   t_class u_class(.*);
`ifdef UNSUP
   t_method u_method(.*);
`endif
   `endif

   t_cstmt u_cstmt;

   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      // a, b, c
      a <= ~a;
      if (cyc % 2 == 0) b <= ~b;
      else c <= ~c;
      // v
      if (cyc % 3 == 0) v[0] <= 1;
      else v <= v << 1;
      // i, j
      i <= i + 2;
      if (cyc % 2 == 0) j <= j + 4;
      // t
      t[cyc % 5] <= t[cyc % 5] + cyc;
      // q
      q.push_front(cyc);
      `WRITE_VERBOSE(("[%0t] values: clk=%b, cyc=%0d, a=%b, b=%b, v=%b, i=%0x, j=%0x, t=[%0x, %0x, %0x, %0x, %0x], obj.k=%0x\n",
                      $time, clk, cyc, a, b, v, i, j, t[0], t[1], t[2], t[3], t[4], k));
      `WRITE_VERBOSE(("              q=%p\n", q));
      if (cyc == 20) begin
          $write("*-* All Finished *-*\n");
          $finish;
      end
   end

endmodule
