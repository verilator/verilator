// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   // Speced ignored: system calls.  I think this is nasty, so we error instead.

   // Speced Illegal: inout/output/ref not allowed
   localparam B1 = f_bad_output(1,2);
   function integer f_bad_output(input [31:0] a, output [31:0] o);
      f_bad_output = 0;
   endfunction

   // Speced Illegal: void

   // Speced Illegal: dotted
   localparam EIGHT = 8;
   localparam B2 = f_bad_dotted(2);
   function integer f_bad_dotted(input [31:0] a);
      f_bad_dotted = t.EIGHT;
   endfunction

   // Speced Illegal: ref to non-local var
   integer modvar;
   localparam B3 = f_bad_nonparam(3);
   function integer f_bad_nonparam(input [31:0] a);
      f_bad_nonparam = modvar;
   endfunction

   // Speced Illegal: needs constant function itself

   // Our own - infinite loop
   localparam B4 = f_bad_infinite(3);
   function integer f_bad_infinite(input [31:0] a);
      while (1) begin
         f_bad_infinite = 0;
      end
   endfunction

   // Our own - stop
   localparam BSTOP = f_bad_stop(3);
   function integer f_bad_stop(input [31:0] a);
      $stop;
   endfunction

   // Verify $fatal works with sformatf as argument
   localparam BFATAL = f_bad_fatal(3);
   function integer f_bad_fatal(input [31:0] a);
      for (integer i=0;i<3;i++) begin
         $display("Printing in loop: %s", $sformatf("%d", i));
      end
      $fatal(2, "%s", $sformatf("Fatal Error"));
   endfunction
endmodule
