// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Johan Bjork.
// SPDX-License-Identifier: CC0-1.0

interface simple_bus #(PARAMETER = 0);
   typedef struct packed {
      logic [31:0] data;
      logic [3:0]  mask;
   } payload_t;

   parameter [6:0] dummy = 22;
   payload_t payload;
   logic [1:0] x;
endinterface

module t ();
   simple_bus sb_intf();
   localparam LP = $bits(sb_intf.payload.data);
   simple_bus #(.PARAMETER($bits(sb_intf.dummy))) simple();
   simple_bus #(.PARAMETER($bits(sb_intf.x))) simple2();
   initial begin
      if (LP != 32) $stop;
      if (simple.PARAMETER != 7) $stop;
      if (simple2.PARAMETER != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
