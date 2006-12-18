// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t_func (/*AUTOARG*/
   // Outputs
   passed, 
   // Inputs
   clk
   );

   // surefire lint_off _NETNM
   // surefire lint_off STMINI

   input clk;
   output passed;  reg passed; initial passed = 0;
   integer _mode;   initial _mode = 0;

   wire [2:0] b3; reg [2:0] g3;
   wire [5:0] b6; reg [5:0] g6;

   t_func_grey2bin #(3) g2b3 (.b(b3), .g(g3));
   t_func_grey2bin #(6) g2b6 (.b(b6), .g(g6));

   always @ (posedge clk) begin
      if (_mode==0) begin
	 _mode <= 1;
	 $write("[%0t] t_func: Running\n",$time);
	 g3 <= 3'b101;
	 g6 <= 6'b110101;
      end
      else if (_mode==1) begin
	 if (b3 !== 3'b110) $stop;
	 if (b6 !== 6'b100110) $stop;
	 $write("[%0t] t_func: Passed\n",$time);
	 passed <= 1'b1;
	 _mode <= 2;
      end
   end

endmodule
