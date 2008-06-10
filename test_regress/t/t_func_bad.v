// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;
   initial begin
      if (add(3'd1) != 0) $stop;  // Too few args
      if (add(3'd1, 3'd2, 3'd3) != 0) $stop;	// Too many args
      x; // Too few args
      if (hasout(3'd1) != 0) $stop;  // outputs
   end

   function [2:0] add;
      input [2:0] from1;
      input [2:0] from2;
      begin
	 add = from1 + from2;
      end
   endfunction

   task x;
      output y;
      begin end
   endtask

   function hasout;
      output [2:0] illegal_output;
      hasout = 0;
   endfunction

endmodule
