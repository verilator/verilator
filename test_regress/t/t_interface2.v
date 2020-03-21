// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   counter_io c1_data();
   counter_io c2_data();
   //counter_io c3_data;	// IEEE illegal, and VCS doesn't allow non-() as it does with cells
   counter_io c3_data();

   counter_ansi  c1 (.clkm(clk),
		     .c_data(c1_data),
		     .i_value(4'h1));
   counter_ansi  c2 (.clkm(clk),
		     .c_data(c2_data),
		     .i_value(4'h2));
`ifdef VERILATOR counter_ansi `else counter_nansi `endif
   /**/ 	 c3 (.clkm(clk),
		     .c_data(c3_data),
		     .i_value(4'h3));

   initial begin
      c1_data.value = 4'h4;
      c2_data.value = 4'h5;
      c3_data.value = 4'h6;
   end

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc<2) begin
	 c1_data.reset <= 1;
	 c2_data.reset <= 1;
	 c3_data.reset <= 1;
      end
      if (cyc==2) begin
	 c1_data.reset <= 0;
	 c2_data.reset <= 0;
	 c3_data.reset <= 0;
      end
      if (cyc==3) begin
	 if (c1_data.get_lcl() != 12345) $stop;
      end
      if (cyc==20) begin
	 $write("[%0t] c1 cyc%0d: c1 %0x %0x  c2 %0x %0x  c3 %0x %0x\n", $time, cyc,
		c1_data.value, c1_data.reset,
		c2_data.value, c2_data.reset,
		c3_data.value, c3_data.reset);
	 if (c1_data.value != 2) $stop;
	 if (c2_data.value != 3) $stop;
	 if (c3_data.value != 4) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

interface counter_io;
   logic [3:0] value;
   logic       reset;
   integer     lcl;
   task set_lcl (input integer a); lcl=a; endtask
   function integer get_lcl (); return lcl; endfunction
endinterface

interface ifunused;
   logic       unused;
endinterface

module counter_ansi
  (
   input clkm,
   counter_io c_data,
   input logic [3:0] i_value
   );

   initial begin
      c_data.set_lcl(12345);
   end

   always @ (posedge clkm) begin
      c_data.value <= c_data.reset ? i_value : c_data.value + 1;
   end
endmodule : counter_ansi

`ifndef VERILATOR
// non-ansi modports not seen in the wild yet.  Verilog-Perl needs parser improvement too.
module counter_nansi(clkm, c_data, i_value);
   input clkm;
   counter_io c_data;
   input logic [3:0] i_value;

   always @ (posedge clkm) begin
      c_data.value <= c_data.reset ? i_value : c_data.value + 1;
   end
endmodule : counter_nansi
`endif

module modunused (ifunused ifinunused);
   ifunused ifunused();
endmodule
