// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire[3:0] #4 val1 = half_cyc;
   wire[3:0] #4 val2;
   reg[3:0] half_cyc = 0;

   assign #4 val2 = half_cyc;

   always @(clk) begin
       if ($time > 0) half_cyc <= half_cyc + 1;
`ifdef TEST_VERBOSE
       $strobe("[%0t] half_cyc=%0d, val1=%0d, val2=%0d", $time, half_cyc, val1, val2);
`endif
       if (half_cyc >= 7) begin
          `checkh(val1, half_cyc - 3);
          `checkh(val2, half_cyc - 7);
       end
       if (half_cyc == 15) begin
           $write("*-* All Finished *-*\n");
           $finish;
       end
   end
endmodule
