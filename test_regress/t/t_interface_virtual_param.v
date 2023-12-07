// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface Bus #(parameter int W = 1, X = 2);
   logic [W-1:0] data;
endinterface

module t;
   Bus#(6, 3) intf1();
   virtual Bus#(6, 3) vintf1 = intf1;

   Bus intf2();
   virtual Bus#(.W(1), .X(2)) vintf2 = intf2;

   initial begin
      intf1.data = '1;
      if (vintf1.data != 6'b111111) $stop;
      if (vintf1.X != 3) $stop;

      intf2.data = '1;
      if (vintf2.data != 1'b1) $stop;
      if (vintf2.X != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
