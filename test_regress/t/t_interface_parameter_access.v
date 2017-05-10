// DESCRIPTION: Verilator: Interface parameter getter
//
// A test of the import parameter used with modport
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader

interface test_if #(parameter integer FOO = 1);

   // Interface variable
   logic 	data;

   // Modport
   modport mp(
              import  getFoo,
	      output  data
	      );

   function integer getFoo ();
      return FOO;
   endfunction

endinterface // test_if


module t (/*AUTOARG*/
	  // Inputs
	  clk
	  );
   input clk;

   test_if #( .FOO (5) ) the_interface ();

   testmod testmod_i (.clk (clk),
		      .intf (the_interface),
                      .intf_no_mp (the_interface)
                      );

endmodule


module testmod
  (
   input clk,
   test_if.mp intf,
   test_if intf_no_mp
   );

`ifdef ELAB_TIME
   localparam THE_FOO = intf.FOO;
   //   localparam THE_OTHER_FOO = intf_no_mp.FOO;
`endif

   always @(posedge clk) begin
`ifdef ELAB_TIME
      if (THE_FOO != 5) begin
         $display("%%Error: THE_FOO = %0d", THE_FOO);
	 $stop;
      end
      //      if (THE_OTHER_FOO != 5) begin
      //         $display("%%Error: THE_OTHER_FOO = %0d", THE_OTHER_FOO);
      //	 $stop;
      //      end
`endif
      if (intf.FOO != 5) begin
         $display("%%Error: intf.FOO = %0d", intf.FOO);
	 $stop;
      end
      //      if (intf_no_mp.FOO != 5) begin
      //         $display("%%Error: intf_no_mp.FOO = %0d", intf_no_mp.FOO);
      //	 $stop;
      //      end
      //      if (i.getFoo() != 5) begin
      //         $display("%%Error: i.getFoo() = %0d", i.getFoo());
      //	 $stop;
      //      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
