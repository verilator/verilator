// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t (/*AUTOARG*/);

   byte dyn [][1:0];

   initial begin
      begin
         dyn = new [3];
         dyn[0] = '{101, 100};
         dyn[1] = '{111, 110};
         dyn[2] = '{121, 120};
`ifndef verilator // bug2314
         `checkh(dyn[0][0], 100);
         `checkh(dyn[0][1], 101);
         `checkh(dyn[1][0], 110);
         `checkh(dyn[1][1], 111);
         `checkh(dyn[2][0], 120);
         `checkh(dyn[2][1], 121);
`endif
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
