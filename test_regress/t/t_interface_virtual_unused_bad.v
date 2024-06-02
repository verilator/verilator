// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Arkadiusz Kozdra.
// SPDX-License-Identifier: CC0-1.0

// See also t_interface_virtual.v

interface QBus;
endinterface

module t (/*AUTOARG*/);

   virtual QBus q8;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
