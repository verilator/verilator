// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   mid, o3,
   // Inputs
   clk, i3
   );
   input clk;
   output logic mid;
   input 	i3;
   output logic o3;

   wire [15:0] temp1;
   wire [15:0] temp1_d1r;

   logic       setbefore;
   always_comb begin
      setbefore = 1'b1;
      if (setbefore) setbefore = 1'b0;  // fine
   end

   always_comb begin
      if (mid)
	temp1 = 'h0;
      else
	temp1 = (temp1_d1r - 'h1);
      mid = (temp1_d1r == 'h0);  // BAD
   end

   always_comb begin
      o3 = 'h0;
      case (i3)
	1'b1: begin
	   o3 = i3;
	end
	default: ;
      endcase
   end

   always_ff @ (posedge clk) begin
      temp1_d1r <= temp1;
   end

endmodule
