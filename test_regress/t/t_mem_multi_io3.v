// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013.
// SPDX-License-Identifier: CC0-1.0

module t
  (
   input logic 				clk,
   input logic 				daten,
   input logic [8:0] 			datval,
   output logic signed [3:0][3:0][35:0] datao
   );

   logic signed [3:0][3:0][3:0][8:0] 	datat;

   genvar 				i;
   generate
      for (i=0; i<4; i++)begin
	 testio dut(.clk(clk), .arr3d_in(datat[i]), .arr2d_out(datao[i]));
      end
   endgenerate

   genvar j;
   generate
      for (i=0; i<4; i++) begin
	 for (j=0; j<4; j++) begin
	    always_comb datat[i][j][0] = daten ? 9'h0 : datval;
	    always_comb datat[i][j][1] = daten ? 9'h1 : datval;
	    always_comb datat[i][j][2] = daten ? 9'h2 : datval;
	    always_comb datat[i][j][3] = daten ? 9'h3 : datval;
	 end
      end
   endgenerate
endmodule

module testio
  (
   input 				clk,
   input logic signed [3:0] [3:0] [8:0] arr3d_in,
   output logic signed [3:0] [35:0] 	arr2d_out
   );
   logic signed [3:0] [35:0] 		ar2d_out_pre;

   always_comb ar2d_out_pre[0][35:0] = {arr3d_in[0][0][8:0], arr3d_in[0][1][8:0], arr3d_in[0][2][8:0], arr3d_in[0][3][8:0]};
   always_comb ar2d_out_pre[0][35:0] = {arr3d_in[0][0][8:0], arr3d_in[0][1][8:0], arr3d_in[0][2][8:0], arr3d_in[0][3][8:0]};
   always_comb ar2d_out_pre[0][35:0] = {arr3d_in[0][0][8:0], arr3d_in[0][1][8:0], arr3d_in[0][2][8:0], arr3d_in[0][3][8:0]};
   always_comb ar2d_out_pre[0][35:0] = {arr3d_in[0][0][8:0], arr3d_in[0][1][8:0], arr3d_in[0][2][8:0], arr3d_in[0][3][8:0]};

   always_ff @(posedge clk) begin
      if (clk)
	arr2d_out <= ar2d_out_pre;
   end

endmodule
