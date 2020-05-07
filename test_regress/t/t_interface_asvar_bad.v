// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   counter_if iface();

   source source (
      .itf  (iface)
   );

endmodule

interface counter_if;
   logic [3:0] value;
endinterface

module source
  (
   counter_if itf
   );

   logic [3:0] getter;

   initial begin
      getter = itf;  // Intended to write itf.value
      getter = 4'd3 + itf;  // Intended to write itf.value
   end

endmodule
