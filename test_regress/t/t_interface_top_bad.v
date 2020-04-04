// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface ifc;
   logic [3:0] value;
   logic       reset;
   modport counter_mp (input reset, output value);
   modport core_mp (output reset, input value);
endinterface

module t
  (// Inputs
   input clk,
   ifc.counter_mp c_data
   );

   integer cyc=1;

endmodule
