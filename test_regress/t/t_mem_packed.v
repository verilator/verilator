// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

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

   // Test for mixed implicit/explicit dimensions and all implicit packed
   bit [3:0][7:0][1:0] vld [1:0][1:0];
   bit [3:0][7:0][1:0] vld2;

   // There are specific nodes for Or, Xor, Xnor and And
   logic            vld_or;
   logic            vld2_or;
   assign vld_or = |vld[0][0];
   assign vld2_or = |vld2;

   logic            vld_xor;
   logic            vld2_xor;
   assign vld_xor = ^vld[0][0];
   assign vld2_xor = ^vld2;

   logic            vld_xnor;
   logic            vld2_xnor;
   assign vld_xnor = ~^vld[0][0];
   assign vld2_xnor = ~^vld2;

   logic            vld_and;
   logic            vld2_and;
   assign vld_and = &vld[0][0];
   assign vld2_and = &vld2;

   // Bit reductions should be cloned, other unary operations should clone the
   // entire assign.
   bit [3:0][7:0][1:0] not_lhs;
   bit [3:0][7:0][1:0] not_rhs;
   assign not_lhs = ~not_rhs;

   // Test an AstNodeUniop that shouldn't be expanded
   bit [3:0][7:0][1:0] vld2_inv;
   assign vld2_inv = ~vld2;

   initial begin
      for (int i=0; i<4; i=i+2) begin
         for (int j=0; j<8; j=j+2) begin
	    vld[0][0][i][j] = 2'b00;
	    vld[0][0][i+1][j+1] = 2'b00;
	    vld2[i][j] = 2'b00;
	    vld2[i+1][j+1] = 2'b00;
	    not_rhs[i][j] = i[1:0];
	    not_rhs[i+1][j+1] = i[1:0];
	 end
      end
   end


   logic [3:0] expect_cyc; initial expect_cyc = 'd15;

   always @(posedge clk) begin
      expect_cyc <= expect_cyc + 1;
      for (int i=0; i<4; i=i+1) begin
         for (int j=0; j<8; j=j+1) begin
	    vld[0][0][i][j] <= vld[0][0][i][j] + 1;
	    vld2[i][j] <= vld2[i][j] + 1;
	    if (not_rhs[i][j] != ~not_lhs[i][j]) $stop;
	    not_rhs[i][j] <= not_rhs[i][j] + 1;
	 end
      end
      if (cyc % 8 == 0) begin
	 vld[0][0][0][0] <= vld[0][0][0][0] - 1;
	 vld2[0][0] <= vld2[0][0] - 1;
      end
      if (expect_cyc < 8 && !vld_xor) $stop;
      else if (expect_cyc > 7 && vld_xor) $stop;

      if (expect_cyc < 8 && vld_xnor) $stop;
      else if (expect_cyc > 7 && !vld_xnor) $stop;

      if (expect_cyc == 15 && vld_or) $stop;
      else if (expect_cyc == 11 && vld_or) $stop;
      else if (expect_cyc != 15 && expect_cyc != 11 && !vld_or) $stop;

      if (expect_cyc == 10 && !vld_and) $stop;
      else if (expect_cyc == 14 && !vld_and) $stop;
      else if (expect_cyc != 10 && expect_cyc != 14 && vld_and) $stop;

      if (vld_xor != vld2_xor) $stop;
      if (vld_xnor != vld2_xnor) $stop;
      if (vld_or != vld2_or) $stop;
      if (vld_and != vld2_and) $stop;
   end

endmodule
