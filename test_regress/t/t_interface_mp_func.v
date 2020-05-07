// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface pads_if();
   modport mp_dig(
                  import        fIn,
                  import        fOut );

   integer exists[8];
   function automatic integer fIn (integer i);
      fIn = exists[i];
   endfunction
   task automatic fOut (integer i);
      exists[i] = 33;
   endtask
endinterface

module t();
   pads_if padsif[1:0]();
   pads_if padsif_arr[1:0]();
   initial begin
      padsif[0].fOut(3);
      if (padsif[0].fIn(3) != 33) $stop;

      padsif_arr[0].fOut(3);
      if (padsif_arr[0].fIn(3) != 33) $stop;
      padsif_arr[1].fOut(3);
      if (padsif_arr[1].fIn(3) != 33) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
