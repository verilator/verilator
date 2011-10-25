// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2011 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   always @(*) begin
      if (clk) begin end
   end

   always @(* ) begin
      if (clk) begin end
   end

   // Not legal in some simulators, legal in others
//   always @(* /*cmt*/ ) begin
//      if (clk) begin end
//   end

   // Not legal in some simulators, legal in others
//   always @(* // cmt
//	    ) begin
//      if (clk) begin end
//   end

   always @ (*
	     ) begin
      if (clk) begin end
   end

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
