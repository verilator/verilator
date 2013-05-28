// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

interface counter_if;
   logic [3:0] value;
   logic       reset;
   modport counter_mp (input reset, output value);
   modport core_mp (output reset, input value);
endinterface

// Check can have inst module before top module
module counter_ansi
  (
   input clkm,
   counter_if c_data,
   input logic [3:0] i_value
   );

   always @ (posedge clkm) begin
      c_data.value <= c_data.reset ? i_value : c_data.value + 1;
   end
endmodule : counter_ansi

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   counter_if c1_data();
   counter_if c2_data();
   counter_if c3_data();
   counter_if c4_data();

   counter_ansi    c1 (.clkm(clk),
		       .c_data(c1_data.counter_mp),
		       .i_value(4'h1));
`ifdef VERILATOR counter_ansi `else counter_nansi `endif
   /**/            c2 (.clkm(clk),
		       .c_data(c2_data.counter_mp),
		       .i_value(4'h2));
   counter_ansi_m  c3 (.clkm(clk),
		       .c_data(c3_data),
		       .i_value(4'h3));
`ifdef VERILATOR counter_ansi_m `else counter_nansi_m `endif
   /**/            c4 (.clkm(clk),
		       .c_data(c4_data),
		       .i_value(4'h4));

   initial begin
      c1_data.value = 4'h4;
      c2_data.value = 4'h5;
      c3_data.value = 4'h6;
      c4_data.value = 4'h7;
   end

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc<2) begin
	 c1_data.reset <= 1;
	 c2_data.reset <= 1;
	 c3_data.reset <= 1;
	 c4_data.reset <= 1;
      end
      if (cyc==2) begin
	 c1_data.reset <= 0;
	 c2_data.reset <= 0;
	 c3_data.reset <= 0;
	 c4_data.reset <= 0;
      end
      if (cyc==20) begin
	 $write("[%0t] cyc%0d: c1 %0x %0x  c2 %0x %0x  c3 %0x %0x  c4 %0x %0x\n", $time, cyc,
		c1_data.value, c1_data.reset,
		c2_data.value, c2_data.reset,
		c3_data.value, c3_data.reset,
		c4_data.value, c4_data.reset);
	 if (c1_data.value != 2) $stop;
	 if (c2_data.value != 3) $stop;
	 if (c3_data.value != 4) $stop;
	 if (c4_data.value != 5) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

`ifndef VERILATOR
// non-ansi modports not seen in the wild yet.  Verilog-Perl needs parser improvement too.
module counter_nansi
  (clkm, c_data, i_value);

   input clkm;
   counter_if c_data;
   input logic [3:0] i_value;

   always @ (posedge clkm) begin
      c_data.value <= c_data.reset ? i_value : c_data.value + 1;
   end
endmodule : counter_nansi
`endif

module counter_ansi_m
  (
   input clkm,
   counter_if.counter_mp c_data,
   input logic [3:0] i_value
   );

   always @ (posedge clkm) begin
      c_data.value <= c_data.reset ? i_value : c_data.value + 1;
   end
endmodule : counter_ansi_m

`ifndef VERILATOR
// non-ansi modports not seen in the wild yet.  Verilog-Perl needs parser improvement too.
module counter_nansi_m
  (clkm, c_data, i_value);

   input clkm;
   counter_if.counter_mp c_data;
   input logic [3:0] i_value;

   always @ (posedge clkm) begin
      c_data.value <= c_data.reset ? i_value : c_data.value + 1;
   end
endmodule : counter_nansi_m
`endif
