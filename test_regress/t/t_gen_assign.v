// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
`timescale 1ns / 1ps

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=0;
   reg [63:0] crc;
   reg [31:0] sum;

   wire [8:0]		Output;
   wire [8:0] 		Input = crc[8:0];

   assigns assigns (/*AUTOINST*/
		    // Outputs
		    .Output		(Output[8:0]),
		    // Inputs
		    .Input		(Input[8:0]));

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x q=%x\n",$time, cyc, crc, sum);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
	 sum <= 32'h0;
      end
      else if (cyc>10 && cyc<90) begin
	 sum <= {sum[30:0],sum[31]} ^ {23'h0, crc[8:0]};
      end
      else if (cyc==99) begin
	 if (sum !== 32'he8bbd130) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module assigns(Input, Output);
   input  [8:0] Input;
   output [8:0] Output;

   genvar 	i;
   generate
      for (i = 0; i < 8; i = i + 1) begin : ap
	 assign Output[(i>0) ? i-1 : 8] = Input[(i>0) ? i-1 : 8];
      end
   endgenerate
endmodule
