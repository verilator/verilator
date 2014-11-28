// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   /*verilator no_inline_module*/   // So we'll get hiearachy we can test
   input clk;

   sub sub (/*AUTOINST*/
	    // Inputs
	    .clk			(clk));
endmodule

module sub (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   /*verilator no_inline_module*/   // So we'll get hiearachy we can test

   integer 	cyc=0;

   reg [127:0] 	save128;
   reg [47:0] 	save48;
   reg [1:0] 	save2;
   reg [255:0] 	cycdone;  // Make sure each cycle executes exactly once
   reg [31:0]	vec[2:1][2:1];
   real		r;
   string	s,s2;

   string 	si;

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d\n",$time, cyc);
`endif
      si = "siimmed";
      cyc <= cyc + 1;
      if (cycdone[cyc[7:0]]) $stop;
      cycdone[cyc[7:0]] <= '1;
      if (cyc==0) begin
	 // Setup
	 save128 <= 128'hc77bb9b3784ea0914afe43fb79d7b71e;
	 save48 <= 48'h4afe43fb79d7;
	 save2 <= 2'b10;
	 vec[1][1] <= 32'h0101;
	 vec[1][2] <= 32'h0102;
	 vec[2][1] <= 32'h0201;
	 vec[2][2] <= 32'h0202;
	 r <= 1.234;
	 s <= "hello";
      end
      if (cyc==1) begin
	 if ($test$plusargs("save_restore")!=0) begin
	    // Don't allow the restored model to run from time 0, it must run from a restore
	    $write("%%Error: didn't really restore\n");
	    $stop;
	 end
      end
      else if (cyc==99) begin
	 if (save128 !== 128'hc77bb9b3784ea0914afe43fb79d7b71e) $stop;
	 if (save48 !== 48'h4afe43fb79d7) $stop;
	 if (save2 !== 2'b10) $stop;
	 if (cycdone !== {{(256-99){1'b0}}, {99{1'b1}}}) $stop;
	 if (vec[1][1] !== 32'h0101) $stop;
	 if (vec[1][2] !== 32'h0102) $stop;
	 if (vec[2][1] !== 32'h0201) $stop;
	 if (vec[2][2] !== 32'h0202) $stop;
	 if (r != 1.234) $stop;
	 $display("%s",s); 
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule
