// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module a;
   a2 a2 (.tmp(1'b0));
   initial begin
      $write("Bad top modules\n");
      $stop;
   end
endmodule

module a2 (input tmp);
   l3 l3 (.tmp(tmp));
endmodule

module b;
   l3 l3 (.tmp(1'b1));
endmodule

module l3 (input tmp);
   initial begin
      if (tmp) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule
