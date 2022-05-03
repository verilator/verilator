// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jonathon Donaldson.
// SPDX-License-Identifier: CC0-1.0

package my_funcs;
   function automatic int simple_func (input int value);
      begin
         simple_func = value;
      end
   endfunction
endpackage

package my_module_types;
   import my_funcs::*;

   localparam MY_PARAM = 3;
   localparam MY_PARAM2 /*verilator public*/ = simple_func(12);
endpackage

module t
  import my_module_types::*;
   (
    input                       i_clk,
    input [MY_PARAM-1:0]        i_d,
    output logic [MY_PARAM-1:0] o_q
    );

   always_ff @(posedge i_clk)
     o_q <= i_d;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
