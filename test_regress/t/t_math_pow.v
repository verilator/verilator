// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [60:0] p;
   reg [60:0] a;
   reg [20:0] b;
   reg [60:0] shifted;

   always @* begin
      p = a[60:0] ** b[20:0];
      shifted = 2 ** b[20:0];
   end

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
`ifdef TEST_VERBOSE
	 $write("%0x %x %x\n", cyc, p, shifted);
`endif
	 // Constant versions
	 if (61'h1 ** 21'h31 != 61'h1) $stop;
	 if (61'h2 ** 21'h10 != 61'h10000) $stop;
	 if (61'd10 ** 21'h3 != 61'h3e8) $stop;
	 if (61'h3  ** 21'h7 != 61'h88b) $stop;
	 if (61'h7ab3811219 ** 21'ha6e30 != 61'h01ea58c703687e81) $stop;
	 if (cyc==1) begin
	    a <= 61'h0;
	    b <= 21'h0;
	 end
	 if (cyc==2) begin
	    a <= 61'h0;
	    b <= 21'h3;
	 end
	 if (cyc==3) begin
	    a <= 61'h1;
	    b <= 21'h31;
	 end
	 if (cyc==4) begin
	    a <= 61'h2;
	    b <= 21'h10;
	 end
	 if (cyc==5) begin
	    a <= 61'd10;
	    b <= 21'd3;
	 end
	 if (cyc==6) begin
	    a <= 61'd3;
	    b <= 21'd7;
	 end
	 if (cyc==7) begin
	    a <= 61'h7ab3811219;
	    b <= 21'ha6e30;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
      case (cyc)
	32'd00: ;
	32'd01: ;
	32'd02: ; // 0^x is indeterminate
	32'd03: ; // 0^x is indeterminate
	32'd04: if (p!=61'h1) $stop;
	32'd05: if (p!=61'h10000) $stop;
	32'd06: if (p!=61'h3e8) $stop;
	32'd07: if (p!=61'h88b) $stop;
	32'd08: if (p!=61'h01ea58c703687e81) $stop;
	32'd09: if (p!=61'h01ea58c703687e81) $stop;
	default: $stop;
      endcase
      case (cyc)
	32'd00: ;
	32'd01: ;
	32'd02: if (shifted!=61'h0000000000000001) $stop;
	32'd03: if (shifted!=61'h0000000000000008) $stop;
	32'd04: if (shifted!=61'h0002000000000000) $stop;
	32'd05: if (shifted!=61'h0000000000010000) $stop;
	32'd06: if (shifted!=61'h0000000000000008) $stop;
	32'd07: if (shifted!=61'h0000000000000080) $stop;
	32'd08: if (shifted!=61'h0000000000000000) $stop;
	32'd09: if (shifted!=61'h0000000000000000) $stop;
	default: $stop;
      endcase
   end
endmodule
