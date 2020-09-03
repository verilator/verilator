// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef class paramed_class_t;
typedef class arg_class_t;

virtual class vclass #(type CTYPE_t = arg_class_t);
   pure virtual function void funcname(paramed_class_t #(CTYPE_t) v);
endclass

class paramed_class_t #(type TYPE=int);
endclass

class arg_class_t;
endclass

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
