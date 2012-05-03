// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

//bug591

module t (/*AUTOARG*/);

   function real ABS (real num);
      ABS = (num < 0) ? -num : num;
   endfunction

   function logic range_chk;
      input real last;
      input real period;
      input real cmp;
      range_chk = 0;
      if ( last >= 0 ) begin
         if ( ABS(last - period) > cmp ) begin
	    range_chk = 1;
         end
      end
   endfunction

   function integer ceil;
      input num;
      real  num;
      if (num > $rtoi(num))
	ceil = $rtoi(num) + 1;
      else
	// verilator lint_off REALCVT
	ceil = num;
	// verilator lint_on REALCVT
   endfunction

   initial begin
      if (range_chk(-1.1, 2.2, 3.3) != 1'b0) $stop;
      if (range_chk(1.1, 2.2, 0.3) != 1'b1) $stop;
      if (range_chk(1.1, 2.2, 2.3) != 1'b0) $stop;
      if (range_chk(2.2, 1.1, 0.3) != 1'b1) $stop;
      if (range_chk(2.2, 1.1, 2.3) != 1'b0) $stop;
      if (ceil(-2.1) != -2) $stop;
      if (ceil(2.1) != 3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
