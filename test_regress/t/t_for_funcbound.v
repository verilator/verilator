// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer j;
   integer hit_count;
   reg [63:0] cam_lookup_hit_vector;

   strings strings ();

   task show;
      input [8*8-1:0] str;
      reg [7:0]       char;
      integer 	      loc;
      begin
	 $write("[%0t] ",$time);
	 strings.stringStart(8*8-1);
	 for (char = strings.stringByte(str); !strings.isNull(char); char = strings.stringByte(str)) begin
	    $write("%c",char);
	 end
	 $write("\n");
      end
   endtask


   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    show("hello\000xx");
	 end
	 if (cyc==2) begin
	    show("world\000xx");
	 end
	 if (cyc==4) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule

module strings;
   // **NOT** reentrant, just a test!
   integer index;
   task stringStart;
      input [31:0] bits;
      begin
	 index = (bits-1)/8;
      end
   endtask

   function isNull;
      input [7:0] chr;
      isNull = (chr == 8'h0);
   endfunction

   function [7:0] stringByte;
      input [8*8-1:0] str;
      begin
	 if (index<=0) stringByte=8'h0;
	 else stringByte = str[index*8 +: 8];
	 index = index - 1;
      end
   endfunction
endmodule
