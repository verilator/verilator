// DESCRIPTION: Verilator: Verilog Test module
//
// A test case for struct signal bit selection.
//
// This test is to check that bit selection of multi-dimensional signal inside
// of a packed struct works. Currently +: and -: blow up with packed structs.
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty, 2013 by Jie Xu.

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   typedef struct packed {
       logic [15:0] channel;
       logic [15:0] others;
   } buss_t;

   buss_t     b;

   reg [7:0]  a;
   reg [7:0]  c;
   reg [7:0]  d;

   initial begin
      b = {16'h8765,16'h4321};
      a = b[19:12];			// This works
      c = b[8+:8];			// This fails
      d = b[11-:8];			// This fails
      if ((a == 8'h54) && (c == 8'h43) && (d == 8'h32)) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
      else begin
	 $stop;
      end
   end

endmodule
