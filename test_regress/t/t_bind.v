// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

bit a_finished;
bit b_finished;

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   wire [31:0] o;
   wire        si = 1'b0;

   ExampInst i
     (// Outputs
      .o	(o[31:0]),
      // Inputs
      .i	(1'b0)
      /*AUTOINST*/);

   Prog p (/*AUTOINST*/
	   // Inputs
	   .si				(si));

   always @ (posedge clk) begin
      if (!a_finished) $stop;
      if (!b_finished) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module InstModule (
   output logic [31:0] so,
   input 	 si
   );
   assign so = {32{si}};
endmodule

program Prog (input si);
   initial a_finished = 1'b1;
endprogram

module ExampInst (o,i);
   output logic [31:0] o;
   input  i;

   InstModule instName
     (// Outputs
      .so	(o[31:0]),
      // Inputs
      .si	(i)
      /*AUTOINST*/);

   //bind InstModule Prog instProg
   //    (.si(si));

   // Note is based on context of caller
   bind InstModule Prog instProg
     (/*AUTOBIND*/
      .si      (si));

endmodule

// Check bind at top level
bind InstModule Prog2 instProg2
  (/*AUTOBIND*/
   .si      (si));

// Check program declared after bind
program Prog2 (input si);
   initial b_finished = 1'b1;
endprogram
