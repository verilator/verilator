// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

interface counter_io;
   logic [3:0] value;
   logic       reset;
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   counter_io c1_data();
   counter_io c2_data();

   counter    c1 (.clkm(clk),
		  .c_data(c1_data),
		  .i_value(4'h1));
   counter2   c2 (.clkm(clk),
		  .c_data(c2_data),
		  .i_value(4'h2));

   initial begin
      c1_data.value = 4'h4;
      c2_data.value = 4'h5;
   end

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc<2) begin
	 c1_data.reset <= 1;
	 c2_data.reset <= 1;
      end
      if (cyc==2) begin
	 c1_data.reset <= 0;
	 c2_data.reset <= 0;
      end
      if (cyc==20) begin
	 $write("[%0t] c1 cyc%0d: %0x %0x\n", $time, cyc, c1_data.value, c1_data.reset);
	 $write("[%0t] c2 cyc%0d: %0x %0x\n", $time, cyc, c2_data.value, c2_data.reset);
	 if (c1_data.value != 2) $stop;
	 if (c2_data.value != 3) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module counter
  (
   input clkm,
   counter_io c_data,
   input logic [3:0] i_value
   );

   always @ (posedge clkm) begin
      if (c_data.reset)
	c_data.value <= i_value;
      else
	c_data.value <= c_data.value + 1;
   end
endmodule : counter

module counter2(clkm, c_data, i_value);
   input clkm;
   counter_io c_data;
   input logic [3:0] i_value;

   always @ (posedge clkm) begin
      if (c_data.reset)
	c_data.value <= i_value;
      else
	c_data.value <= c_data.value + 1;
   end
endmodule : counter2
