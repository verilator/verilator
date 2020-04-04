// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   // verilator lint_off MULTIDRIVEN

   ma ma0 ();

   initial t.ma0.u_b[0].f(1);
   initial t.ma0.u_b[0].f(clk);

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
      if (cyc==5) begin
	 ma0.        checkName(ma0.        getName(1'b0));
	 ma0.mb0.    checkName(ma0.mb0.    getName(1'b0));
	 ma0.mb0.mc0.checkName(ma0.mb0.mc0.getName(1'b0));
      end
      if (cyc==9) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

`ifdef ATTRIBUTES
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
`else
 `define INLINE_MODULE
 `define INLINE_MID_MODULE
`endif

module global_mod;
   `INLINE_MODULE
   parameter INITVAL = 0;
   integer globali;

   initial globali = INITVAL;
   function [31:0] getName;  input fake;  getName = "gmod"; endfunction
   function [31:0] getGlob;  input fake;  getGlob = globali;  endfunction
endmodule

module ma ();
   `INLINE_MODULE

   mb #(0) mb0 ();
   reg [31:0] gName; initial gName = "ma  ";
   function [31:0] getName;  input fake;  getName = "ma  "; endfunction
   task checkName; input [31:0] name;  if (name !== "ma  ") $stop; endtask

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

   reg [31:0] gName; initial gName = "mb  ";
   function [31:0] getName;  input fake;  getName = "mb  "; endfunction
   function [31:0] getP2  ;  input fake;  getP2 = P2;       endfunction
   task checkName; input [31:0] name;  if (name !== "mb  ") $stop; endtask

   initial begin
`ifndef verilator #1; `endif
      if (ma. getName(1'b0) !== "ma  ") $stop;
      if (    getName(1'b0) !== "mb  ") $stop;
      if (mc1.getName(1'b0) !== "mc  ") $stop;

      ma. checkName (ma. gName);
      /**/checkName (    gName);
      mc1.checkName (mc1.gName);
      ma. checkName (ma. getName(1'b0));
      /**/checkName (    getName(1'b0));
      mc1.checkName (mc1.getName(1'b0));
   end
endmodule

module mc ();
   `INLINE_MODULE
    parameter P2 = 0;
    parameter P3 = 0;

   reg [31:0] gName; initial gName = "mc  ";
   function [31:0] getName;  input fake;  getName = "mc  "; endfunction
   function [31:0] getP3  ;  input fake;  getP3 = P3;       endfunction
   task checkName; input [31:0] name;  if (name !== "mc  ") $stop; endtask

   initial begin
`ifndef verilator #1; `endif
      if (ma.getName(1'b0) !== "ma  ") $stop;
      if (mb.getName(1'b0) !== "mb  ") $stop;
      if (mc.getName(1'b0) !== "mc  ") $stop;
      ma.checkName (ma.gName);
      mb.checkName (mb.gName);
      mc.checkName (mc.gName);
      ma.checkName (ma.getName(1'b0));
      mb.checkName (mb.getName(1'b0));
      mc.checkName (mc.getName(1'b0));
   end
endmodule

module b;

   function void f(bit v);
      $display("%m");
   endfunction : f;

endmodule : b

bind ma b u_b[0:1];
