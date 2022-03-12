// DESCRIPTION: Verilator: Dotted reference that uses another dotted reference
// as the select expression
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg;
   localparam PKG_PARAM = 1;
endpackage
package PkgImp;
   import Pkg::*;
   export Pkg::*;
endpackage

class Cls;
   int member = 1;
   function void method;
   endfunction
endclass

interface Iface;
   logic ifsig;
   modport mp(input ifsig);
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk, in
   );
   input clk;
   input in;

   // verilator lint_off UNPACKED

   typedef enum {
                 ZERO,
                 ONE = 1
   } e_t;

   typedef struct packed {
      e_t a;
   } ps_t;
   typedef struct {
      logic signed [2:0] a;
   } us_t;
   typedef union {
      logic a;
   } union_t;

   const ps_t ps[3];
   us_t us;
   union_t unu;

   int            array[3];
   initial array = '{1,2,3};

   reg [15:0]     pubflat /*verilator public_flat_rw @(posedge clk) */;

   reg [15:0]    pubflat_r;
   wire [15:0]    pubflat_w = pubflat;
   int            fd;
   int            i;

   int            q[$];
   int            assoc[string];
   int            dyn[];

   task t;
      $display("stmt");
   endtask
   function int f(input int v);
      $display("stmt");
      return v == 0 ? 99 : ~v + 1;
   endfunction

   sub sub();

   initial begin
      int other;
      begin //unnamed
         for (int i = 0; i < 3; ++i) begin
            other = f(i);
            $display("stmt %d %d", i, other);
            t();
         end
      end
      begin : named
         $display("stmt");
      end : named
   end
   final begin
      $display("stmt");
   end

   always @ (in) begin
      $display("stmt");
   end
   always @ (posedge clk) begin
      $display("posedge clk");
      pubflat_r <= pubflat_w;
   end
   always @ (negedge clk) begin
      $display("negedge clk, pfr = %x", pubflat_r);
   end

   int cyc;
   int fo;
   int sum;
   real r;
   string str;
   always_ff @ (posedge clk) begin
      cyc <= cyc + 1;
      r <= r + 0.01;
      fo = cyc;
      sub.inc(fo, sum);
      sum = sub.f(sum);
      $display("[%0t] sum = %d", $time, sum);
      $display("a?= %d", $c(1) ? $c32(20) : $c32(30));

      $c(";");
      $display("%d", $c("0"));
      fd = $fopen("/dev/null");
      $fclose(fd);
      fd = $fopen("/dev/null", "r");
      $fgetc(fd);  //  stmt
      $fflush(fd);
      $fscanf(fd, "%d", sum);
      $fdisplay("i = ", sum);
      $fwrite(fd, "hello");
      $readmemh(fd, array);
      $readmemh(fd, array, 0);
      $readmemh(fd, array, 0, 0);

      sum = 0;
      for (int i = 0; i < cyc; ++i) begin
         sum += i;
         if (sum > 10) break;
         else sum += 1;
      end
      if (cyc == 99) $finish;
      if (cyc == 100) $stop;

      case (in)  // synopsys full_case parallel_case
        1: $display("1");
        default: $display("default");
      endcase
      priority case (in)
        1: $display("1");
        default: $display("default");
      endcase
      unique case (in)
        1: $display("1");
        default: $display("default");
      endcase
      unique0 case (in)
        1: $display("1");
        default: $display("default");
      endcase
      if (in) $display("1"); else $display("0");
      priority if (in) $display("1"); else $display("0");
      unique if (in) $display("1"); else $display("0");
      unique0 if (in) $display("1"); else $display("0");

      $display($past(cyc), $past(cyc, 1));

      str = $sformatf("cyc=%d", cyc);
      $display("str = %s", str);
      $display("%% [%t] [%t] to=%o td=%d", $time, $realtime, $time, $time);
      $sscanf("foo=5", "foo=%d", i);
      $printtimescale;
      if (i != 5) $stop;

      sum = $random;
      sum = $random(10);
      sum = $urandom;
      sum = $urandom(10);

      if (Pkg::PKG_PARAM != 1) $stop;
      sub.r = 62.0;

      $display("%g", $log10(r));
      $display("%g", $ln(r));
      $display("%g", $exp(r));
      $display("%g", $sqrt(r));
      $display("%g", $floor(r));
      $display("%g", $ceil(r));
      $display("%g", $sin(r));
      $display("%g", $cos(r));
      $display("%g", $tan(r));
      $display("%g", $asin(r));
      $display("%g", $acos(r));
      $display("%g", $atan(r));
      $display("%g", $sinh(r));
      $display("%g", $cosh(r));
      $display("%g", $tanh(r));
      $display("%g", $asinh(r));
      $display("%g", $acosh(r));
      $display("%g", $atanh(r));

      force sum = 10;
      repeat (2) if (sum != 10) $stop;
      release sum;
   end
endmodule

module sub();
   task inc(input int i, output int o);
      o = {1'b0, i[31:1]} + 32'd1;
   endtask
   function int f(input int v);
      if (v == 0) return 33;
      return {31'd0, v[2]} + 32'd1;
   endfunction
   real r;
endmodule

package p;
   logic pkgvar;
endpackage
