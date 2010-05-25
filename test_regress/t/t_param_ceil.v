// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

module t (/*AUTOARG*/);

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [31:0]		O_out;			// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .O_out			(O_out[31:0]));

   initial begin
      if (O_out != 32'h4) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module Test
  (
   output [31:0] O_out
   );

   test
     #(
       .pFOO(5),
       .pBAR(2)
       ) U_test
       (
	.O_out(O_out)
	);
endmodule

module test
  #(parameter pFOO = 7,
    parameter pBAR = 3,
    parameter pBAZ = ceiling(pFOO, pBAR)
    )
   (
    output [31:0] O_out
    );

   assign O_out = pBAZ;

   function integer ceiling;
      input [31:0] x, y;
      ceiling = ((x%y == 0) ? x/y : (x/y)+1) + 1;
   endfunction
endmodule
