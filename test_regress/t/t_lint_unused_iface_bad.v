// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface dummy_if ();
   logic sig_udrv;
   logic sig_uusd;
endinterface: dummy_if

module sub
  (
   dummy_if dummy
   );

   assign dummy.sig_uusd = 1'b0 | dummy.sig_udrv;
endmodule


module t (/*AUTOARG*/);

   dummy_if dummy ();

   sub sub
     (.dummy(dummy)
      );

endmodule
