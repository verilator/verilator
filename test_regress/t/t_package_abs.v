// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// see bug491

package functions;
   function real abs (real num);
      abs = (num <0) ? -num : num;
   endfunction
   function real neg (real num);
      return -abs(num);  // Check package funcs can call package funcs
   endfunction
endpackage

module t ();
   import functions::*;
   localparam P = 1;
   generate
      if (P == 1) begin
	 initial begin
	    if (abs(-2.1) != 2.1) $stop;
	    if (abs(2.2) != 2.2) $stop;
	    if (neg(-2.1) != -2.1) $stop;
	    if (neg(2.2) != -2.2) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   endgenerate
endmodule
