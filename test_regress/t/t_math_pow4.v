// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Clifford Wolf.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;

   wire [31:0] y;
   reg 	       a;
   test004 sub (/*AUTOINST*/
		// Outputs
		.y			(y[31:0]),
		// Inputs
		.a			(a));

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d a=%x y=%x\n",$time, cyc, a, y);
`endif
      cyc <= cyc + 1;
      if (cyc==0) begin
	 a <= 0;
      end
      else if (cyc==1) begin
	 a <= 1;
	 if (y != 32'h0) $stop;
      end
      else if (cyc==2) begin
	 if (y != 32'h010000ff) $stop;
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module test004(a, y);
  input a;
  output [31:0] y;

  wire [7:0] y0;
  wire [7:0] y1;
  wire [7:0] y2;
  wire [7:0] y3;
  assign y = {y0,y1,y2,y3};

  localparam [7:0] v0 = +8'sd1 ** -8'sd2; //'h01
  localparam [7:0] v1 = +8'sd2 ** -8'sd2; //'h00
  localparam [7:0] v2 = -8'sd2 ** -8'sd3; //'h00
  localparam [7:0] v3 = -8'sd1 ** -8'sd3; //'hff
  localparam [7:0] zero = 0;

   initial $display("v0=%x v1=%x v2=%x v3=%x", v0,v1,v2,v3);

  assign y0 = a ? v0 : zero;
  assign y1 = a ? v1 : zero;
  assign y2 = a ? v2 : zero;
  assign y3 = a ? v3 : zero;
endmodule
