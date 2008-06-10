// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (clk);
   input clk;

   reg [63:0] inwide;
   reg [39:0] addr;

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write ("%x %x\n", cyc, addr);
`endif
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    addr <= 40'h12_3456_7890;
	 end
	 if (cyc==2) begin
	    if (addr !== 40'h1234567890) $stop;
	    addr[31:0] <= 32'habcd_efaa;
	 end
	 if (cyc==3) begin
	    if (addr !== 40'h12abcdefaa) $stop;
	    addr[39:32] <= 8'h44;
	    inwide <= 64'hffeeddcc_11334466;
	 end
	 if (cyc==4) begin
	    if (addr !== 40'h44abcdefaa) $stop;
	    addr[31:0] <= inwide[31:0];
	 end
	 if (cyc==5) begin
	    if (addr !== 40'h4411334466) $stop;
	    $display ("Flip [%x]\n", inwide[3:0]);
	    addr[{2'b0,inwide[3:0]}] <= ! addr[{2'b0,inwide[3:0]}];
	 end
	 if (cyc==6) begin
	    if (addr !== 40'h4411334426) $stop;
	 end
	 if (cyc==10) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
