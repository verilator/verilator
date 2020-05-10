// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

module t (/*AUTOARG*/);

   parameter int sliceddn[7:0] = '{'h100, 'h101, 'h102, 'h103, 'h104, 'h105, 'h106, 'h107};
   parameter int slicedup[0:7] = '{'h100, 'h101, 'h102, 'h103, 'h104, 'h105, 'h106, 'h107};
   int alldn[7:0];
   int allup[0:7];
   int twodn[1:0];
   int twoup[0:1];

   initial begin
      `checkh(sliceddn[7], 'h100);
      alldn[7:0] = sliceddn[7:0];
      `checkh(alldn[7], 'h100);
      alldn[7:0] = sliceddn[0 +: 8];  // down: lsb/lo +: width
      `checkh(alldn[7], 'h100);
      alldn[7:0] = sliceddn[7 -: 8];  // down: msb/hi -: width
      `checkh(alldn[7], 'h100);
      twodn[1:0] = sliceddn[6:5];
      `checkh(twodn[1], 'h101);
      `checkh(twodn[0], 'h102);
      twodn[1:0] = sliceddn[4 +: 2];
      `checkh(twodn[1], 'h102);
      `checkh(twodn[0], 'h103);
      twodn[1:0] = sliceddn[4 -: 2];
      `checkh(twodn[1], 'h103);
      `checkh(twodn[0], 'h104);

      `checkh(slicedup[7], 'h107);
      allup[0:7] = slicedup[0:7];
      `checkh(alldn[7], 'h100);
      allup[0:7] = slicedup[0 +: 8];  // up: msb/lo +: width
      `checkh(alldn[7], 'h100);
      allup[0:7] = slicedup[7 -: 8];  // up: lsb/hi -: width
      `checkh(alldn[7], 'h100);
      twoup[0:1] = slicedup[5:6];
      `checkh(twoup[1], 'h106);
      `checkh(twoup[0], 'h105);
      twoup[0:1] = slicedup[4 +: 2];
      `checkh(twoup[1], 'h105);
      `checkh(twoup[0], 'h104);
      twoup[0:1] = slicedup[4 -: 2];
      `checkh(twoup[1], 'h104);
      `checkh(twoup[0], 'h103);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
