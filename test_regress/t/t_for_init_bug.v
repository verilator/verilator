// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   priority_mask,
   // Inputs
   muxed_requests
   );

   parameter ARW = 7;

   // verilator lint_off UNOPTFLAT
   integer i,j;

   output reg [ARW-1:0] priority_mask;

   input [ARW-1:0] muxed_requests;

   always @* begin
      for (i=ARW-1;i>0;i=i-1) begin
	 priority_mask[i]=1'b0;
	 //   vvvv=== note j=j not j=i; was bug
	 for( j=j;j>=0;j=j-1)
	   priority_mask[i]=priority_mask[j] | muxed_requests[j];
      end
      //Bit zero is always enabled
      priority_mask[0]=1'b0;
   end
   
endmodule

// Local Variables:
// verilog-auto-inst-param-value: t
// End:
