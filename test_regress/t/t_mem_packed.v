// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   //Simple debug:
   //wire  [1:1] wir_a [3:3] [2:2]; //11
   //logic [1:1] log_a [3:3] [2:2]; //12
   //wire  [3:3] [2:2] [1:1] wir_p; //13
   //logic [3:3] [2:2] [1:1] log_p; //14

   integer cyc; initial cyc = 0;
`ifdef iverilog
   reg [7:0] arr [3:0];
   wire [7:0] arr_w [3:0];
`else
   reg [3:0] [7:0] arr;
   wire [3:0] [7:0] arr_w;
`endif
   reg [7:0] sum;
   reg [7:0] sum_w;
   integer    i0;

   initial begin
      for (i0=0; i0<5; i0=i0+1) begin
	 arr[i0] = 1 << (i0[1:0]*2);
      end
   end

   assign arr_w = arr;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==0) begin
	 // Setup
	 sum <= 0;
	 sum_w <= 0;
      end
      else if (cyc >= 10 && cyc < 14) begin
	 sum <= sum + arr[cyc-10];

	 sum_w <= sum_w + arr_w[cyc-10];
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d sum=%x\n",$time, cyc, sum);
	 if (sum != 8'h55) $stop;
	 if (sum != sum_w) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

   // Test ordering of packed dimensions
   logic             [31:0] data_out;
   logic             [31:0] data_out2;
   logic [0:0] [2:0] [31:0] data_in;
   logic [31:0] data_in2 [0:0] [2:0];
   assign data_out = data_in[0][0] + data_in[0][1] + data_in[0][2];
   assign data_out2 = data_in2[0][0] + data_in2[0][1] + data_in2[0][2];

   logic [31:0] last_data_out;
   always @ (posedge clk) begin
      if (cyc <= 2) begin
	 data_in[0][0] <= 0;
	 data_in[0][1] <= 0;
	 data_in[0][2] <= 0;
	 data_in2[0][0] <= 0;
	 data_in2[0][1] <= 0;
	 data_in2[0][2] <= 0;
      end
      else if (cyc > 2 && cyc < 99) begin
	 data_in[0][0] <= data_in[0][0] + 1;
	 data_in[0][1] <= data_in[0][1] + 1;
	 data_in[0][2] <= data_in[0][2] + 1;
	 data_in2[0][0] <= data_in2[0][0] + 1;
	 data_in2[0][1] <= data_in2[0][1] + 1;
	 data_in2[0][2] <= data_in2[0][2] + 1;
	 last_data_out <= data_out;
`ifdef TEST_VERBOSE
	 $write("data_out %0x %0x\n", data_out, last_data_out);
`endif
	 if (cyc > 4 && data_out != last_data_out + 3) $stop;
	 if (cyc > 4 && data_out != data_out2) $stop;
      end
   end

endmodule
