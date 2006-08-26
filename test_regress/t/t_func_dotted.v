// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   
   // verilator lint_off MULTIDRIVEN

   ma ma0 ();

   global_mod #(32'hf00d) global_cell ();
   global_mod #(32'hf22d) global_cell2 ();

   input clk;
   integer cyc=1;

   function [31:0] getName;  input fake;  getName = "t   "; endfunction

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==2) begin
	 if (global_cell. getGlob(1'b0)  !== 32'hf00d) $stop;
	 if (global_cell2.getGlob(1'b0) !== 32'hf22d) $stop;
      end
      if (cyc==3) begin
	 if (ma0.        getName(1'b0) !== "ma  ") $stop;
	 if (ma0.mb0.    getName(1'b0) !== "mb  ") $stop;
	 if (ma0.mb0.mc0.getName(1'b0) !== "mc  ") $stop;
      end
      if (cyc==4) begin
	 if (ma0.mb0.    getP2(1'b0) !== 32'h0) $stop;
	 if (ma0.mb0.mc0.getP3(1'b0) !== 32'h0) $stop;
	 if (ma0.mb0.mc1.getP3(1'b0) !== 32'h1) $stop;
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
   integer global;

   initial global = INITVAL;
   function [31:0] getName;  input fake;  getName = "gmod"; endfunction
   function [31:0] getGlob;  input fake;  getGlob = global;  endfunction
endmodule

module ma ();
   `INLINE_MODULE

   mb #(0) mb0 ();
   function [31:0] getName;  input fake;  getName = "ma  "; endfunction

   initial begin
      if (ma.getName(1'b0) !== "ma  ") $stop;
      if (mb0.getName(1'b0) !== "mb  ") $stop;
      if (mb0.mc0.getName(1'b0) !== "mc  ") $stop;
   end
endmodule

module mb ();
   `INLINE_MID_MODULE
   parameter P2 = 0;

   mc #(P2,0) mc0 ();
   mc #(P2,1) mc1 ();
   global_mod #(32'hf33d) global_cell2 ();

   function [31:0] getName;  input fake;  getName = "mb  "; endfunction
   function [31:0] getP2  ;  input fake;  getP2 = P2;       endfunction

   initial begin
      if (ma.getName(1'b0) !== "ma  ") $stop;
      if (getName(1'b0) !== "mb  ") $stop;
      if (mc1.getName(1'b0) !== "mc  ") $stop;
   end
endmodule

module mc ();
   `INLINE_MODULE
    parameter P2 = 0;
    parameter P3 = 0;

   function [31:0] getName;  input fake;  getName = "mc  "; endfunction
   function [31:0] getP3  ;  input fake;  getP3 = P3;       endfunction

   initial begin
      if (ma.getName(1'b0) !== "ma  ") $stop;
      if (mb.getName(1'b0) !== "mb  ") $stop;
      if (mc.getName(1'b0) !== "mc  ") $stop;
   end
endmodule
