// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.

module secret #(parameter GATED_CLK = 0)
              (
               input [31:0] 		 accum_in,
               output wire [31:0] 	 accum_out,
               input 			 accum_bypass,
               output [31:0] 		 accum_bypass_out,
               input 			 s1_in,
               output logic 		 s1_out,
               input [1:0] 		 s2_in,
               output logic [1:0] 	 s2_out,
               input [7:0] 		 s8_in,
               output logic [7:0] 	 s8_out,
               input [32:0] 		 s33_in,
               output logic [32:0] 	 s33_out,
               input [63:0] 		 s64_in,
               output logic [63:0] 	 s64_out,
               input [64:0] 		 s65_in,
               output logic [64:0] 	 s65_out,
               input [128:0] 		 s129_in,
               output logic [128:0] 	 s129_out,
               input [3:0] [31:0] 	 s4x32_in,
               output logic [3:0] [31:0] s4x32_out,
               input                     clk_en,
               input 			 clk);

   logic [31:0] 			 secret_accum_q = 0;
   logic [31:0] 			 secret_value = 7;

   initial $display("created %m");

   wire the_clk = GATED_CLK != 0 ? clk & clk_en : clk;
   always @(posedge the_clk) begin
      secret_accum_q <= secret_accum_q + accum_in + secret_value;
   end

   // Test combinatorial paths of different sizes
   always @(*) begin
      s1_out = s1_in;
      s2_out = s2_in;
      s8_out = s8_in;
      s64_out = s64_in;
      s65_out = s65_in;
      s129_out = s129_in;
      s4x32_out = s4x32_in;
   end

   sub sub (.sub_in(s33_in), .sub_out(s33_out));

   // Test sequential path
   assign accum_out = secret_accum_q;

   // Test mixed combinatorial/sequential path
   assign accum_bypass_out = accum_bypass ? accum_in : secret_accum_q;

   final $display("destroying %m");

endmodule

module sub (
            input [32:0]  sub_in,
            output [32:0] sub_out);

   /*verilator no_inline_module*/

   assign sub_out = sub_in;

endmodule
