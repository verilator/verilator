// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t;
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

endmodule

module InstModule (
   output logic [31:0] so,
   input 	 si
   );
   assign so = {32{si}};
endmodule

program Prog (input si);
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
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

