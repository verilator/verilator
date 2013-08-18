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
      //
      f(.j(1), .no_such(2)); // Name mismatch
      f(.dup(1), .dup(3)); // Duplicate
      f(1,2,3); // Too many
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

   function int f( int j = 1, int dup = 0 );
      return (j<<16) | dup;
   endfunction

endmodule
