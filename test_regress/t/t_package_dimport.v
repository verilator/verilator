// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

package defs;
   function automatic integer max;
      input integer a;
      input integer b;
      max = (a > b) ? a : b;
   endfunction

   function automatic integer log2;
      input integer value;
      value = value >> 1;
      for (log2 = 0; value > 0; log2 = log2 + 1)
        value = value >> 1;
   endfunction

   function automatic integer ceil_log2;
      input integer value;
      value = value - 1;
      for (ceil_log2 = 0; value > 0; ceil_log2 = ceil_log2 + 1)
        value = value >> 1;
   endfunction
endpackage

module sub();

   import defs::*;

   parameter RAND_NUM_MAX          = "";

   localparam DATA_RANGE           = RAND_NUM_MAX + 1;
   localparam DATA_WIDTH           = ceil_log2(DATA_RANGE);
   localparam WIDTH                = max(4, ceil_log2(DATA_RANGE + 1));

endmodule

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   import defs::*;

   parameter WHICH          = 0;
   parameter MAX_COUNT      = 10;

   localparam MAX_EXPONENT         = log2(MAX_COUNT);
   localparam EXPONENT_WIDTH       = ceil_log2(MAX_EXPONENT + 1);

   input                           clk;

   generate
      if (WHICH == 1)
	begin : which_true
           sub sub_true();
           defparam sub_true.RAND_NUM_MAX   = MAX_EXPONENT;
	end
      else
	begin : which_false
           sub sub_false();
           defparam sub_false.RAND_NUM_MAX   = MAX_COUNT;
	end
   endgenerate

endmodule
