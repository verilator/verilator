// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   fastclk
   );
   input fastclk;

   t_netlist tnetlist
     (.also_fastclk	(fastclk),
      /*AUTOINST*/
      // Inputs
      .fastclk				(fastclk));

endmodule

module t_netlist (/*AUTOARG*/
   // Inputs
   fastclk, also_fastclk
   );

   // surefire lint_off ASWEMB

   input fastclk;
   input also_fastclk;
   integer _mode; initial _mode = 0;

   // This entire module should optimize to nearly nothing...

   // verilator lint_off UNOPTFLAT
   reg [4:0] a,a2,b,c,d,e;
   // verilator lint_on UNOPTFLAT

   initial a=5'd1;

   always @ (posedge fastclk) begin
      b <= a+5'd1;
      c <= b+5'd1; // Better for ordering if this moves before previous statement
   end

   // verilator lint_off UNOPT
   always @ (d or /*AS*/a or c) begin
      e = d+5'd1;
      a2 = a+5'd1; // This can be pulled out of the middle of the always
      d = c+5'd1;  // Better for ordering if this moves before previous statement
   end
   // verilator lint_on UNOPT

   always @ (posedge also_fastclk) begin
      if (_mode==5) begin
	 if (a2 != 5'd2) $stop;
	 if (e != 5'd5) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
      _mode <= _mode + 1;
   end

endmodule
