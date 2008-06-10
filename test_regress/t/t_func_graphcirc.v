// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

module t (clk);
   input clk;

   integer cyc; initial cyc=0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
	 ReadContDisps;
      end
      else if (cyc == 5) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
`ifndef verilator
      DispContDisps;
`endif
   end

   task ReadContDisps;
      begin
	 $display("%m: Here: %d", cyc);
      end
   endtask

   integer dindex;

   task DispContDisps;
      /* verilator public */
      begin
	 if (cyc >= 2) begin
            if ( cyc >= 4 ) begin
	       dindex = dindex + 2; //*** Error line
	       $display("%m: DIndex increment %d", cyc);
	       $c("cout<<\"Hello1?\"<<endl;");
            end
	    $c("cout<<\"Hello2?\"<<endl;");
	    $c("cout<<\"Hello3?\"<<endl;");
	 end
      end
   endtask

endmodule
