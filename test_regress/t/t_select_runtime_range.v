// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   reg [43:0] mi;
   reg [5:0]  index;
   integer    indexi;
   reg	      read;

   initial begin
      // Static
      mi = 44'b01010101010101010101010101010101010101010101;
      if (mi[0] !== 1'b1) $stop;
      if (mi[1 -: 2] !== 2'b01) $stop;
`ifdef VERILATOR
      // verilator lint_off SELRANGE
      if (mi[-1] !== 1'bx && mi[-1] !== 1'b0) $stop;
      if (mi[0 -: 2] !== 2'b1x && 1'b0) $stop;
      if (mi[-1 -: 2] !== 2'bxx && 1'b0) $stop;
      // verilator lint_on SELRANGE
`else
      if (mi[-1] !== 1'bx) $stop;
      if (mi[0 -: 2] !== 2'b1x) $stop;
      if (mi[-1 -: 2] !== 2'bxx) $stop;
`endif
   end

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    mi = 44'h123;
	 end
	 if (cyc==2) begin
	    index = 6'd43;
	    indexi = 43;
	 end
	 if (cyc==3) begin
	    read = mi[index];
	    if (read!==1'b0) $stop;
	    read = mi[indexi];
	    if (read!==1'b0) $stop;
	 end
	 if (cyc==4) begin
	    index = 6'd44;
	    indexi = 44;
	 end
	 if (cyc==5) begin
	    read = mi[index];
	    $display("-Illegal read value: %x",read);
	    //if (read!==1'b1 && read!==1'bx) $stop;
	    read = mi[indexi];
	    $display("-Illegal read value: %x",read);
	    //if (read!==1'b1 && read!==1'bx) $stop;
	 end
	 if (cyc==6) begin
	    indexi = -1;
	 end
	 if (cyc==7) begin
	    read = mi[indexi];
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
