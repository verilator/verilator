// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;


   reg [31:0] r32;
   wire [3:0] w4;
   wire [4:0] w5;

   assign     w4 = NUMONES_8 ( r32[7:0]  );
   assign     w5 = NUMONES_16( r32[15:0] );

   function [3:0] NUMONES_8;
      input   [7:0]           i8;
      reg     [7:0]           i8;
      begin
         NUMONES_8 = 4'b1;
      end
   endfunction // NUMONES_8

   function [4:0] NUMONES_16;
      input   [15:0]          i16;
      reg     [15:0]          i16;
      begin
         NUMONES_16 = ( NUMONES_8( i16[7:0] ) +  NUMONES_8( i16[15:8] ));
      end
   endfunction

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    r32 <= 32'h12345678;
	 end
	 if (cyc==2) begin
	    if (w4 !== 1) $stop;
	    if (w5 !== 2) $stop;
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule
