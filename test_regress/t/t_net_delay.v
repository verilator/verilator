// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t;
   // verilator lint_off UNOPTFLAT
   // verilator lint_off PROCASSINIT
   logic clk = 0;
   // verilator lint_on UNOPTFLAT
   // verilator lint_on PROCASSINIT
   always #2 clk = ~clk;

   // verilator lint_off UNDRIVEN
   wire[3:0] x;
   // verilator lint_on UNDRIVEN
   bit [3:0] cyc;
   wire[3:0] #3 val1;
   wire[3:0] #3 val2;
   wire[3:0] #5 val3 = cyc;
   wire[3:0] #5 val4;
   wire[3:0] #3 val5 = x, val6 = cyc;

   assign val1 = cyc;
   assign #3 val2 = cyc;
   assign val4 = cyc;
   assign val5 = cyc;

   always @(posedge clk) begin
       if ($time > 0) cyc <= cyc + 1;
       if (cyc == 15) begin
           $write("*-* All Finished *-*\n");
           $finish;
       end
   end

   always @(posedge clk) #1 begin
`ifdef TEST_VERBOSE
      $display("[%0t] cyc=%0d val1=%0d val2=%0d val3=%0d val4=%0d val5=%0d val6=%0d",
               $time, cyc, val1, val2, val3, val4, val5, val6);
`endif
      if (cyc >= 3) begin
          `checkh(val1, cyc - 1);
          `checkh(val2, cyc - 2);
          `checkh(val3, 0);
          `checkh(val4, 0);
          `checkh(val5, cyc);
          `checkh(val6, cyc - 1);
       end
    end
endmodule
