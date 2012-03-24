// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   // verilator lint_off MULTIDRIVEN

   wire [31:0] outb0c0;
   wire [31:0] outb0c1;
   wire [31:0] outb1c0;
   wire [31:0] outb1c1;

   reg [7:0]   lclmem [7:0];

   ma ma0 (.outb0c0(outb0c0), .outb0c1(outb0c1),
	   .outb1c0(outb1c0), .outb1c1(outb1c1)
	   );

   global_mod #(32'hf00d) global_cell ();
   global_mod #(32'hf22d) global_cell2 ();

   input clk;
   integer cyc=1;
   always @ (posedge clk) begin
      cyc <= cyc + 1;
`ifdef TEST_VERBOSE
      $write("[%0t] cyc%0d: %0x %0x %0x %0x\n", $time, cyc, outb0c0, outb0c1, outb1c0, outb1c1);
`endif
      if (cyc==2) begin
	 if (global_cell.globali  != 32'hf00d) $stop;
	 if (global_cell2.globali != 32'hf22d) $stop;
	 if (outb0c0 != 32'h00) $stop;
	 if (outb0c1 != 32'h01) $stop;
	 if (outb1c0 != 32'h10) $stop;
	 if (outb1c1 != 32'h11) $stop;
      end
      if (cyc==3) begin
	 // Can we scope down and read and write vars?
	 ma0.mb0.mc0.out <= ma0.mb0.mc0.out + 32'h100;
	 ma0.mb0.mc1.out <= ma0.mb0.mc1.out + 32'h100;
	 ma0.mb1.mc0.out <= ma0.mb1.mc0.out + 32'h100;
	 ma0.mb1.mc1.out <= ma0.mb1.mc1.out + 32'h100;
      end
      if (cyc==4) begin
	 // Can we do dotted's inside array sels?
	 ma0.rmtmem[ma0.mb0.mc0.out[2:0]] = 8'h12;
	 lclmem[ma0.mb0.mc0.out[2:0]] = 8'h24;
	 if (outb0c0 != 32'h100) $stop;
	 if (outb0c1 != 32'h101) $stop;
	 if (outb1c0 != 32'h110) $stop;
	 if (outb1c1 != 32'h111) $stop;
      end
      if (cyc==5) begin
	 if (ma0.rmtmem[ma0.mb0.mc0.out[2:0]] != 8'h12) $stop;
	 if (lclmem[ma0.mb0.mc0.out[2:0]] != 8'h24) $stop;
	 if (outb0c0 != 32'h1100) $stop;
	 if (outb0c1 != 32'h2101) $stop;
	 if (outb1c0 != 32'h2110) $stop;
	 if (outb1c1 != 32'h3111) $stop;
      end
      if (cyc==6) begin
	 if (outb0c0 != 32'h31100) $stop;
	 if (outb0c1 != 32'h02101) $stop;
	 if (outb1c0 != 32'h42110) $stop;
	 if (outb1c1 != 32'h03111) $stop;
      end
      if (cyc==9) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

`ifdef USE_INLINE_MID
 `define INLINE_MODULE /*verilator inline_module*/
 `define INLINE_MID_MODULE /*verilator no_inline_module*/
`else
 `ifdef USE_INLINE
  `define INLINE_MODULE /*verilator inline_module*/
  `define INLINE_MID_MODULE /*verilator inline_module*/
 `else
  `define INLINE_MODULE /*verilator public_module*/
  `define INLINE_MID_MODULE /*verilator public_module*/
 `endif
`endif

module global_mod;
   `INLINE_MODULE
   parameter INITVAL = 0;
   integer globali;
   initial globali = INITVAL;
endmodule

module ma (
    output wire [31:0] outb0c0,
    output wire [31:0] outb0c1,
    output wire [31:0] outb1c0,
    output wire [31:0] outb1c1
	   );
   `INLINE_MODULE

     reg [7:0] rmtmem [7:0];

   mb #(0) mb0 (.outc0(outb0c0), .outc1(outb0c1));
   mb #(1) mb1 (.outc0(outb1c0), .outc1(outb1c1));
endmodule

module mb (
    output wire [31:0] outc0,
    output wire [31:0] outc1
   );
   `INLINE_MID_MODULE
   parameter P2 = 0;
   mc #(P2,0) mc0 (.out(outc0));
   mc #(P2,1) mc1 (.out(outc1));
   global_mod #(32'hf33d) global_cell2 ();

   wire        reach_up_clk = t.clk;
   always @(reach_up_clk) begin
      if (P2==0) begin // Only for mb0
	 if (outc0 !== t.ma0.mb0.mc0.out) $stop; // Top module name and lower instances
	 if (outc0 !==   ma0.mb0.mc0.out) $stop; // Upper module name and lower instances
	 if (outc0 !==   ma .mb0.mc0.out) $stop; // Upper module name and lower instances
	 if (outc0 !==        mb.mc0.out) $stop; // This module name and lower instances
	 if (outc0 !==       mb0.mc0.out) $stop; // Upper instance name and lower instances
	 if (outc0 !==           mc0.out) $stop; // Lower instances

	 if (outc1 !== t.ma0.mb0.mc1.out) $stop; // Top module name and lower instances
	 if (outc1 !==   ma0.mb0.mc1.out) $stop; // Upper module name and lower instances
	 if (outc1 !==   ma .mb0.mc1.out) $stop; // Upper module name and lower instances
	 if (outc1 !==        mb.mc1.out) $stop; // This module name and lower instances
	 if (outc1 !==       mb0.mc1.out) $stop; // Upper instance name and lower instances
	 if (outc1 !==           mc1.out) $stop; // Lower instances
      end
   end
endmodule

module mc (output reg [31:0] out);
   `INLINE_MODULE
   parameter P2 = 0;
   parameter P3 = 0;
   initial begin
      out = {24'h0,P2[3:0],P3[3:0]};
      //$write("%m P2=%0x p3=%0x out=%x\n",P2, P3, out);
   end

   // Can we look from the top module name down?
   wire [31:0] reach_up_cyc = t.cyc;

   always @ (posedge t.clk) begin
      //$write("[%0t] %m: Got reachup, cyc=%0d\n", $time, reach_up_cyc);
      if (reach_up_cyc==2) begin
	 if (global_cell.globali != 32'hf00d) $stop;
	 if (global_cell2.globali != 32'hf33d) $stop;
      end
      if (reach_up_cyc==4) begin
	 out[15:12] <= {P2[3:0]+P3[3:0]+4'd1};
      end
      if (reach_up_cyc==5) begin
	 // Can we set another instance?
	 if (P3==1) begin  // Without this, there are two possible correct answers...
	    mc0.out[19:16] <= {mc0.out[19:16]+P2[3:0]+P3[3:0]+4'd2};
	    $display("%m Set %x->%x   %x %x %x %x",mc0.out, {mc0.out[19:16]+P2[3:0]+P3[3:0]+4'd2}, mc0.out[19:16],P2[3:0],P3[3:0],4'd2);
	 end
      end
   end
endmodule
