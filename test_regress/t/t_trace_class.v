// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

class Cls #(parameter int PARAM);
   static int s_cls_static = 123;
endclass

module top();
   typedef Cls#(.PARAM(0)) Cls_t;

   Cls_t obj;

   initial begin
      obj = new;
`ifdef verilator
      obj.s_cls_static = $c("100");  // no-opt
`else
      obj.s_cls_static = 100;
`endif
      if (obj.s_cls_static != 100) $stop;
      if (obj.PARAM != 0) $stop;
      $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
      $dumpvars(0);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
