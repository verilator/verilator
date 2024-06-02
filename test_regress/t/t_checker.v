// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d\n", $time, cyc);
`endif
      cyc <= cyc + 1;
      if (cyc == 0) begin
      end
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   Chk check(clk, cyc);

endmodule

checker Chk
            // UNSUP  (input clk, int in)
            ;
   bit clk;
   bit in;
   bit rst;
   rand bit randed;  // TODO test this

   int counter = 0;

   int ival;
   final if (ival != 1234) $stop;
   genvar g;
   if (0) begin
      initial ival = 1;
   end
   else begin
      initial ival = 1234;
   end

   int ival2;
   case (1)
     0: initial ival2 = 0;
     default: initial ival2 = 12345;
   endcase
   final if (ival2 != 12345) $stop;


   default clocking clk;  // TODO test this
   default disable iff rst;  // TODO test this

   checker ChkChk;  // TODO flag unsupported
   endchecker

   function automatic int f;  // TODO test this
   endfunction


   clocking cb1 @(posedge clk);  // TODO test this
       input in;
       output out;
   endclocking

   always_ff @(posedge clk)
      counter <= counter + 1'b1;

   a1: assert property (@(posedge clk) counter == in);
endchecker
