// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   tpub p1 (.clk(clk), .i(32'd1));
   tpub p2 (.clk(clk), .i(32'd2));

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==1) begin
`ifdef verilator
	    $c("publicTop();");
`endif
	 end
	 if (cyc==20) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

   task publicTop;
      // verilator public
      // We have different optimizations if only one of something, so try it out.
      $write("Hello in publicTop\n");
   endtask

endmodule

module tpub (
	     input clk,
	     input [31:0] i);

   reg [23:0] var_long;
   reg [59:0] var_quad;
   reg [71:0] var_wide;
   reg 	      var_bool;

   // verilator lint_off BLKANDNBLK
   reg [11:0] var_flop;
   // verilator lint_on  BLKANDNBLK

   reg [23:0] got_long /*verilator public*/;
   reg [59:0] got_quad /*verilator public*/;
   reg [71:0] got_wide /*verilator public*/;
   reg        got_bool /*verilator public*/;

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 // cyc==1 is in top level
	 if (cyc==2) begin
	    publicNoArgs;
	    publicSetBool(1'b1);
	    publicSetLong(24'habca);
	    publicSetQuad(60'h4444_3333_2222);
	    publicSetWide(72'h12_5678_9123_1245_2352);
	    var_flop <= 12'habe;
	 end
	 if (cyc==3) begin
	    if (1'b1 != publicGetSetBool(1'b0)) $stop;
	    if (24'habca != publicGetSetLong(24'h1234)) $stop;
	    if (60'h4444_3333_2222 != publicGetSetQuad(60'h123_4567_89ab)) $stop;
	    if (72'h12_5678_9123_1245_2352 != publicGetSetWide(72'hac_abca_aaaa_bbbb_1234)) $stop;
	 end
	 if (cyc==4) begin
	    publicGetBool(got_bool);
	    if (1'b0 != got_bool) $stop;
	    publicGetLong(got_long);
	    if (24'h1234 != got_long) $stop;
	    publicGetQuad(got_quad);
	    if (60'h123_4567_89ab != got_quad) $stop;
	    publicGetWide(got_wide);
	    if (72'hac_abca_aaaa_bbbb_1234 != got_wide) $stop;
	 end
	 //
`ifdef VERILATOR_PUBLIC_TASKS
	 if (cyc==11) begin
	    $c("publicNoArgs();");
	    $c("publicSetBool(true);");
	    $c("publicSetLong(0x11bca);");
	    $c("publicSetQuad(VL_ULL(0x66655554444));");
	    $c("publicSetFlop(0x321);");
	    //Unsupported: $c("WData w[3] = {0x12, 0x5678_9123, 0x1245_2352}; publicSetWide(w);");
	 end
	 if (cyc==12) begin
	    $c("got_bool = publicGetSetBool(true);");
	    $c("got_long = publicGetSetLong(0x11bca);");
	    $c("got_quad = publicGetSetQuad(VL_ULL(0xaaaabbbbcccc));");
	 end
	 if (cyc==13) begin
	    $c("{ bool gb; publicGetBool(gb); got_bool=gb; }");
	    if (1'b1 != got_bool) $stop;
	    $c("publicGetLong(got_long);");
	    if (24'h11bca != got_long) $stop;
	    $c("{ vluint64_t qq; publicGetQuad(qq); got_quad=qq; }");
	    if (60'haaaa_bbbb_cccc != got_quad) $stop;
	    $c("{ WData gw[3]; publicGetWide(gw); VL_ASSIGN_W(72,got_wide,gw); }");
	    if (72'hac_abca_aaaa_bbbb_1234 != got_wide) $stop;
	    //Below doesn't work, because we're calling it inside the loop that sets var_flop
	    // if (12'h321 != var_flop) $stop;
	 end
	 if (cyc==14) begin
	    if ($c32("publicInstNum()") != i) $stop;
	 end
`endif
      end
   end

   task publicEmpty;
      // verilator public
      begin end
   endtask

   task publicNoArgs;
      // verilator public
      $write("Hello in publicNoArgs\n");
   endtask

   task publicSetBool;
      // verilator public
      input in_bool;
      var_bool = in_bool;
   endtask

   task publicSetLong;
      // verilator public
      input [23:0] in_long;
      reg [23:0]   not_long;
      begin
	 not_long = ~in_long;	// Test that we can have local variables
	 var_long = ~not_long;
      end
   endtask

   task publicSetQuad;
      // verilator public
      input [59:0] in_quad;
      var_quad = in_quad;
   endtask

   task publicSetFlop;
      // verilator public
      input [11:0] in_flop;
      var_flop = in_flop;
   endtask

   task publicSetWide;
      // verilator public
      input [71:0] in_wide;
      var_wide = in_wide;
   endtask

   task publicGetBool;
      // verilator public
      output out_bool;
      out_bool = var_bool;
   endtask

   task publicGetLong;
      // verilator public
      output [23:0] out_long;
      out_long = var_long;
   endtask

   task publicGetQuad;
      // verilator public
      output [59:0] out_quad;
      out_quad = var_quad;
   endtask

   task publicGetWide;
      // verilator public
      output [71:0] out_wide;
      out_wide = var_wide;
   endtask

   function publicGetSetBool;
      // verilator public
      input in_bool;
      begin
	 publicGetSetBool = var_bool;
	 var_bool = in_bool;
      end
   endfunction

   function [23:0] publicGetSetLong;
      // verilator public
      input [23:0] in_long;
      begin
	 publicGetSetLong = var_long;
	 var_long = in_long;
      end
   endfunction

   function [59:0] publicGetSetQuad;
      // verilator public
      input [59:0] in_quad;
      begin
	 publicGetSetQuad = var_quad;
	 var_quad = in_quad;
      end
   endfunction

   function [71:0] publicGetSetWide;
      // Can't be public, as no wide return types in C++
      input [71:0] in_wide;
      begin
	 publicGetSetWide = var_wide;
	 var_wide = in_wide;
      end
   endfunction

`ifdef VERILATOR_PUBLIC_TASKS
   function [31:0] publicInstNum;
      // verilator public
      publicInstNum = i;
   endfunction
`endif

endmodule
