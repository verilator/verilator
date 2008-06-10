// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;

   // Check that the lint_on is obeyed.
   // verilator lint_off VARHIDDEN
   // verilator lint_on  VARHIDDEN

   integer top;

   task x;
      output top;
      begin end
   endtask

   initial begin
      begin: lower
	 integer top;
      end
   end

endmodule
