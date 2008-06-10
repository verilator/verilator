// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t_rnd(/*AUTOARG*/
   // Outputs
   passed,
   // Inputs
   clk
   );

   input clk;
   output passed;  reg passed; initial passed = 0;
   reg 	 _ranit;

   reg [2:0] a;
   reg [33:0] wide;
   // surefire lint_off UDDSCN
   reg 	      unused_r;
   // surefire lint_on  UDDSCN

   // surefire lint_off STMINI
   initial _ranit = 0;

   always @ (posedge clk) begin : blockName
      begin	// Verify begin/begin is legal
	 unused_r <= 1'b1;
      end
      begin end	// Verify empty is legal
   end

   wire one = 1'b1;
   wire [7:0] rand_bits = 8'b01xx_xx10;

   always @ (posedge clk) begin
      if (!_ranit) begin
	 _ranit <= 1;
	 $write("[%0t] t_rnd: Running\n", $time);
	 //
	 a = 3'b1xx;
	 wide <= 34'bx1_00000000_xxxxxxxx_00000000_xxxx0000;
	 $write("[%0t] t_rnd: Value %b %b\n", $time, a, wide[31:0]);
	 if (one !== 1'b1) $stop;
	 if ((rand_bits & 8'b1100_0011) !== 8'b0100_0010) $stop;
	 //
	 $write("[%0t] t_rnd: Passed\n", $time);
	 passed <= 1'b1;
      end
   end

   // surefire lint_off UDDSDN
   // verilator lint_off UNUSED
   wire _unused_ok = |{1'b1, wide};
   // verilator lint_on  UNUSED

endmodule
