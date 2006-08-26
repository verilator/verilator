// $Id:$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   integer j;
   integer hit_count;
   reg [63:0] cam_lookup_hit_vector;

   always @(/*AUTOSENSE*/cam_lookup_hit_vector) begin
      hit_count = 0;
      for (j=0; j < 64; j=j+1) begin
	 hit_count = hit_count + {31'h0, cam_lookup_hit_vector[j]};
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

   always @ (posedge clk) begin
      cam_lookup_hit_vector <= 0;
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
	    cam_lookup_hit_vector <= 64'h00010000_00010000;
	 end
	 if (cyc==2) begin
	    if (hit_count != 32'd2) $stop;
	    cam_lookup_hit_vector <= 64'h01010010_00010001;
	 end
	 if (cyc==3) begin
	    if (hit_count != 32'd5) $stop;
	    if (wide_for_count != 32'h80) $stop;
	 end
	 if (cyc==4) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule

// Local Variables:
// compile-command: "./vlint __FILE__"
// End:
