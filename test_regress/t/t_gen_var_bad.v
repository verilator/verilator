// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t;
   integer i;
   generate
      for (i=0; i<3; i=i+1) begin	// Bad: i is not a genvar
      end
   endgenerate
endmodule
