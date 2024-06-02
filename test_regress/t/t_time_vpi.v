// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`timescale `time_scale_units / `time_scale_prec

import "DPI-C" function void dpii_check();

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   // verilator lint_off REALCVT
   time      digits = 5432109876.543210ns;  // Will round to time units
   realtime rdigits = 5432109876.543210ns;  // Will round to time precision
   time     high_acc = 64'd12345678901234567890;  // Would lose accuracy if calculated in double
   // verilator lint_on REALCVT

   always @ (posedge clk) begin
      cyc <= cyc + 1;
`ifdef TEST_VERBOSE
      $write("- [%0t] tick\n", $time);
`endif
      if ($time >= 60) begin
         $write(":: In %m\n");
         $printtimescale;
         $write("[%0t] time%%0d=%0d  123%%0t=%0t\n", $time, $time, 123);
         $write("  dig%%0t=%0t dig%%0d=%0d\n", digits, digits);
         $write("  rdig%%0t=%0t rdig%%0f=%0f\n", rdigits, rdigits);
         $write("  acc%%0t=%0t acc%%0d=%0d\n", high_acc, high_acc);
         $timeformat(-9, 6, "ns", 16);
         $write("[%0t] time%%0d=%0d  123%%0t=%0t\n", $time, $time, 123);
         $write("  dig%%0t=%0t dig%%0d=%0d\n", digits, digits);
         $write("  rdig%%0t=%0t rdig%%0f=%0f\n", rdigits, rdigits);
         $write("  acc%%0t=%0t acc%%0d=%0d\n", high_acc, high_acc);
         $write("[%0t] stime%%0t=%0t  stime%%0d=%0d  stime%%0f=%0f\n",
                $time, $stime, $stime, $stime);
         // verilator lint_off REALCVT
         $write("[%0t] rtime%%0t=%0t  rtime%%0d=%0d  rtime%%0f=%0f\n",
                $time, $realtime, $realtime, $realtime);
         // verilator lint_on REALCVT
         dpii_check();
         $write("*-* All Finished *-*\n");
         $finish;
      end

   end
endmodule
