// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

interface counter_io;
   logic [3:0] value;
   logic       reset;
   modport counter_side (input reset, output value);
   modport core_side (output reset, input value);
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk,
   counter_io.counter_side c_data
   );

   input clk;
   integer cyc=1;

endmodule
