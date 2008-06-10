// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;

   integer top;

   initial begin
      begin : a
	 integer lower;
	 lower = 1;
	 top = 1;
	 if (lower != 1) $stop;
	 begin : aa
	    integer lev2;
	    lev2 = 1;
	    lower = 2;
	    top = 2;
	 end
	 if (lower != 2) $stop;
      end
      begin : b
	 integer lower;
	 lower = 1;
	 top = 2;
	 begin : empty
	    begin : empty
	    end
	 end
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
