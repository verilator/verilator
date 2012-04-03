// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

// bug475

module t();

   function real get_real_one;
      input 	      ignored;
      get_real_one = 1.1;
   endfunction

   localparam R_PARAM = get_real_one(1'b0);
   localparam R_PARAM_2 = (R_PARAM > 0);

   generate
      initial begin
	 if (R_PARAM != 1.1) $stop;
	 if (R_PARAM_2 != 1'b1) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   endgenerate

endmodule
