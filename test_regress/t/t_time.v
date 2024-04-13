// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Paul Wright.
// SPDX-License-Identifier: CC0-1.0

/* Working through the $time example from IEEE Std 1364-2005
** Section 17.7.1
** The example uses a 10ns timeunit with a 1ns timeprecision
** For 16ns $time should return 2
** For 32ns $time should return 3
**/

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t ();
   timeunit 10ns;
   timeprecision 1ns;

   longint should_be_2, should_be_3;
   real should_be_1p6, should_be_3p2;

   initial begin : initial_blk1
      should_be_2 = 0;
      should_be_3 = 0;
      #(16ns);
      $display("$time=%0t=%0d, $realtime=%g", $time(), $time(), $realtime());
      should_be_2 = $time();
      should_be_1p6 = $realtime();
      #(16ns);
      $display("$time=%0t=%0d, $realtime=%g", $time(), $time(), $realtime());
      should_be_3 = $time();
      should_be_3p2 = $realtime();
      #(16ns);
      $finish(1);
    end

   initial begin : initial_blk2
      #(100ns);
      $display("%%Error: We should not get here");
      $stop;
   end

   function bit real_chk(input real tvar, input real evar);
      real diff;
      diff = tvar - evar;
      return (diff < 1e-9) && (diff > -1e-9);
   endfunction

   final begin : last_blk
      $display("Info: should_be_2 = %0d", should_be_2);
      $display("Info: should_be_3 = %0d", should_be_3);
      `checkd(should_be_2, 2);
      `checkd(should_be_3, 3);

      chk_2 :   assert(should_be_2 == 2);
      chk_3 :   assert(should_be_3 == 3);
      chk_1p6 : assert(real_chk(should_be_1p6, 1.6));
      chk_3p2 : assert(real_chk(should_be_3p2, 3.2));
      $write("*-* All Finished *-*\n");
     end

endmodule
