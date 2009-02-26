// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/);

   reg signed [2:0] negcnt;
   integer times;
   integer repeats;
   initial begin
      times = 0;
      repeat (1) begin
	 repeat (0) $stop;
	 repeat (-1) $stop;
	 negcnt = 'sb111;
	 repeat (negcnt) $stop;
	 repeat (5) begin
	    repeat (2) begin
	       times = times + 1;
	    end
	 end
      end
      if (times != 10) $stop;
      //
      repeats = 0;
      forever begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
