// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire[3:0] #4 val1 = cyc;
   wire[3:0] #4 val2;
   reg[3:0] cyc = 0;

   assign #4 val2 = cyc;

   always @(posedge clk) begin
       cyc <= cyc + 1;
`ifdef TEST_VERBOSE
       $write("[%0t] cyc=%0d, val1=%0d, val2=%0d\n", $time, cyc, val1, val2);
`endif
       if (cyc >= 7) begin
          `checkh(val1, cyc - 1);
          `checkh(val2, cyc - 7);
       end
       if (cyc == 15) begin
           $write("*-* All Finished *-*\n");
           $finish;
       end
   end
endmodule
