// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

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
