// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`begin_keywords "VAMS-2.3"

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   task check (integer line, real got, real expec);
      real delta;
      delta = got-expec;
      if (delta > 0.001) begin
	 $display("Line%d:  Got %g Exp %g\n", line, got, expec);
	 $stop;
      end
   endtask

   wreal wr;
   assign wr = 1.1;

   sub sub (.*);

   initial begin
      check(`__LINE__, sqrt(2.0)	, 1.414);
      check(`__LINE__, pow(2.0,2.0)	, 4.0);
      check(`__LINE__, ln(2.0)		, 0.693147);
      check(`__LINE__, log(2.0)		, 0.30103);
      check(`__LINE__, floor(2.5)	, 2.0);
      check(`__LINE__, exp(2.0)		, 7.38906);
      check(`__LINE__, ceil(2.5)	, 3.0);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub (
	    input wreal wr
	    );
   initial begin
      if (wr != 1.1) $stop;
   end
endmodule
