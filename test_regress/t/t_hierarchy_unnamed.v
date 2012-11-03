// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Chandan Egbert.

module sub();
endmodule

module t(input logic a, input logic b,
	 output logic x, output logic y);

   always_comb begin
      integer i;
      x = a;
   end

   sub u0();

   always_comb begin
      integer j;
      y = b;
   end

endmodule
