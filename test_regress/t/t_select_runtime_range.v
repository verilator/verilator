// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (clk);
   input clk;

   reg [43:0] mi;
   reg [5:0]  index;
   reg	      read;

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    mi = 44'h123;
	 end
	 if (cyc==2) begin
	    index = 6'd43;
	 end
	 if (cyc==3) begin
	    read = mi[index];
	    if (read!==1'b0) $stop;
	 end
	 if (cyc==4) begin
	    index = 6'd44;
	 end
	 if (cyc==5) begin
	    read = mi[index];
	    $display("-Illegal read value: %x",read);
	    //if (read!==1'b1 && read!==1'bx) $stop;
	 end
	 if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
