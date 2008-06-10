// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer _mode;

   reg	       _guard1;
   reg [127:0] r_wide0;
   reg 	       _guard2;
   wire [63:0] r_wide1;
   reg 	       _guard3;
   reg 	       _guard4;
   reg 	       _guard5;
   reg 	       _guard6;

   assign      r_wide1 = r_wide0[127:64];

   // surefire lint_off STMINI
   initial _mode = 0;

   always @ (posedge clk) begin
      if (_mode==0) begin
	 $write("[%0t] t_equal: Running\n", $time);
	 _guard1 <= 0;
 	 _guard2 <= 0;
 	 _guard3 <= 0;
 	 _guard4 <= 0;
 	 _guard5 <= 0;
 	 _guard6 <= 0;

	 _mode<=1;
	 r_wide0 <= {32'h aa111111,32'hbb222222,32'hcc333333,32'hdd444444};
      end
      else if (_mode==1) begin
	 _mode<=2;
	 //
	 if (5'd10 != 5'b1010) $stop;
	 if (5'd10 != 5'd10) $stop;
	 if (5'd10 != 5'ha) $stop;
	 if (5'd10 != 5'o12) $stop;
	 if (5'd10 != 5'B 1010) $stop;
	 if (5'd10 != 5'D10) $stop;
	 if (5'd10 != 5'H a) $stop;
	 if (5'd10 != 5 'O 12) $stop;
	 //
	 if (r_wide0 !== {32'haa111111,32'hbb222222,32'hcc333333,32'hdd444444}) $stop;
	 if (r_wide1 !== {32'haa111111,32'hbb222222}) $stop;
	 if (|{_guard1,_guard2,_guard3,_guard4,_guard5,_guard6}) begin
	    $write("Guard error %x %x %x %x %x\n",_guard1,_guard2,_guard3,_guard4,_guard5);
	    $stop;
	 end
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
