// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`begin_keywords "VAMS-2.3"

module t (/*autoarg*/
   // Inputs
   clk, in
   );

   input clk;

   input [15:0] in;
   wreal aout;

   integer 	cyc=0;

   real 	vin;
   wreal 	vpass;
   through through (.vin, .vpass);

   real 	gnd;
   wire 	out;
   within_range within_range (/*AUTOINST*/
			      // Interfaces
			      .vpass		(vpass),
			      .gnd		(gnd),
			      // Outputs
			      .out		(out));

    // wreal bus declaration
    wreal vin_upper_bus[1:0];

    // wreal nets declaration
    wreal vout_split_0;
    wreal vout_split_1;

    wreal_bus wreal_bus( .vin_bus(vin_upper_bus[1:0]),
                         .vout_split_0(vout_split_0),
                         .vout_split_1(vout_split_1));


    // implicit declaration of wreal
`ifdef VERILATOR
   wreal wreal_implicit_net;  // implicit declaration of wreal not supported yet
`endif
   // verilator lint_off IMPLICIT
   first_level first_level(.in(cyc[0]), .out(wreal_implicit_net));
   // verilator lint_on IMPLICIT

   parameter real lsb = 1;
   // verilator lint_off WIDTH
   assign  aout = $itor(in) * lsb;
   // verilator lint_on WIDTH

   always @ (posedge clk) begin
      cyc <= cyc + 1;
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d aout=%d (%f-%f=%f)\n",$time, cyc, out, vin, gnd, within_range.in_int);
`endif
      if (cyc==0) begin
	 // Setup
	 gnd = 0.0;
	 vin = 0.2;
      end
      else if (cyc==2) begin
	 if (out != 0) $stop;
      end
      else if (cyc==3) begin
	 gnd = 0.0;
	 vin = 0.6;
      end
      else if (cyc==4) begin
	 if (out != 1) $stop;
      end
      else if (cyc==5) begin
	 gnd = 0.6;
	 vin = 0.8;
      end
      else if (cyc==6) begin
	 if (out != 0) $stop;
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module through
  (input wreal vin,
   output wreal vpass);
   assign vpass = vin;
endmodule

module within_range
  (input wreal vpass,
   input wreal gnd,
   output out);

   parameter real V_MIN = 0.5;
   parameter real V_MAX = 10;

   wreal in_int = vpass - gnd;
   assign out = (V_MIN <= in_int && in_int <= V_MAX);
endmodule


module wreal_bus
  (input wreal vin_bus [1:0],
   output wreal vout_split_0,
   output wreal vout_split_1);
   assign vout_split_0 = vin_bus[0];
   assign vout_split_1 = vin_bus[1];
endmodule

module first_level
  (input in,
`ifdef VERILATOR
   output wreal out
`else
   output out  // Implicity becomes real
`endif
);
   second_level second_level(.in(in), .out(out));
endmodule

module second_level(in, out);
   input in;
   output out;
   wreal out;
   assign out = in ? 1.23456: 7.8910;
endmodule
