// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);
   initial begin
      bit[3:0] arr[] = '{25{4'b1000}};
      bit [99:0] bit100;

      bit100 = { >> bit {arr} };
      `checkh(bit100[3:0], 4'b1000);
      bit100 = { << bit {arr} };
      `checkh(bit100[3:0], 4'b0001);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
