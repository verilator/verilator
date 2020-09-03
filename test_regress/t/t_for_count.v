// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   integer j;
   reg [63:0] cam_lookup_hit_vector;

   integer hit_count;
   always @(/*AUTOSENSE*/cam_lookup_hit_vector) begin
      hit_count = 0;
      for (j=0; j < 64; j=j+1) begin
	 hit_count = hit_count + {31'h0, cam_lookup_hit_vector[j]};
      end
   end

   integer hit_count2;
   always @(/*AUTOSENSE*/cam_lookup_hit_vector) begin
      hit_count2 = 0;
      for (j=63; j >= 0; j=j-1) begin
	 hit_count2 = hit_count2 + {31'h0, cam_lookup_hit_vector[j]};
      end
   end

   integer hit_count3;
   always @(/*AUTOSENSE*/cam_lookup_hit_vector) begin
      hit_count3 = 0;
      for (j=63; j > 0; j=j-1) begin
	 if (cam_lookup_hit_vector[j]) hit_count3 = hit_count3 + 32'd1;
      end
   end

   reg [127:0] wide_for_index;
   reg [31:0]  wide_for_count;
   always @(/*AUTOSENSE*/cam_lookup_hit_vector) begin
      wide_for_count = 0;
      for (wide_for_index = 128'hff_00000000_00000000;
	   wide_for_index < 128'hff_00000000_00000100;
	   wide_for_index = wide_for_index + 2) begin
	 wide_for_count = wide_for_count+32'h1;
      end
   end

   // While loop
   integer w;
   initial begin
      while (w<10) w=w+1;
      if (w!=10) $stop;
      while (w<20) begin w=w+2; end
      while (w<20) begin w=w+99999; end  // NEVER
      if (w!=20) $stop;
   end

   // Do-While loop
   integer dw;
   initial begin
      do dw=dw+1; while (dw<10);
      if (dw!=10) $stop;
      do dw=dw+2; while (dw<20);
      if (dw!=20) $stop;
      do dw=dw+5; while (dw<20);  // Once
      if (dw!=25) $stop;
   end

   always @ (posedge clk) begin
      cam_lookup_hit_vector <= 0;
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    cam_lookup_hit_vector <= 64'h00010000_00010000;
	 end
	 if (cyc==2) begin
	    if (hit_count != 32'd2) $stop;
	    if (hit_count2 != 32'd2) $stop;
	    if (hit_count3 != 32'd2) $stop;
	    cam_lookup_hit_vector <= 64'h01010010_00010001;
	 end
	 if (cyc==3) begin
	    if (hit_count != 32'd5) $stop;
	    if (hit_count2 != 32'd5) $stop;
	    if (hit_count3 != 32'd4) $stop;
	    if (wide_for_count != 32'h80) $stop;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule
