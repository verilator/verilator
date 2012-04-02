// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

// see bug 474
package functions;
   localparam LP_PACK = 512;
   localparam LP_PACK_AND_MOD = 19;
   task check_param;
      $display("In %m\n");  // "In functions::check_param"
      if (LP_PACK_AND_MOD != 19) $stop;
   endtask
endpackage

module t ();
   // synthesis translate off
   import functions::*;
   // synthesis translate on
   localparam LP_PACK_AND_MOD = 20;
   initial begin
      #10;
      if (LP_PACK_AND_MOD != 20) $stop;
      check_param();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

						