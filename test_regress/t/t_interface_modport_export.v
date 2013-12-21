// DESCRIPTION: Verilator: Verilog Test module
//
// A test of the export parameter used with modport
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Jeremy Bennett.

interface test_if;

   // Pre-declare function
   extern function myfunc (input logic val);

   // Interface variable
   logic 	data;

   // Modport
   modport mp_e(
              export  myfunc,
	      output  data
	      );

   // Modport
   modport mp_i(
              import  myfunc,
	      output  data
	      );

endinterface // test_if


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   test_if i ();

   testmod_callee testmod_callee_i (.ie (i.mp_e));
   testmod_caller testmod_caller_i (.clk (clk),
				    .ii (i.mp_i));
endmodule


module testmod_callee
  (
   test_if.mp_e  ie
   );

   function automatic logic ie.myfunc (input logic val);
      begin
	 myfunc = (val == 1'b0);
      end
   endfunction
endmodule // testmod_caller


module testmod_caller
  (
   input clk,
   test_if.mp_i  ii
   );

   always @(posedge clk) begin
      ii.data = 1'b0;
      if (ii.myfunc (1'b0)) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
      else begin
	 $stop;
      end
   end
endmodule
