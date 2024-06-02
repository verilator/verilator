// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
   bit x;
} p_struct_t;

module p_mh (inout p_struct_t p_i, inout p_struct_t p_o);
   // OK: module p_mh (input p_struct_t p_i, output p_struct_t p_o);
   assign p_o.x = p_i.x;
endmodule

module t;
   p_struct_t p_i, p_o;

   p_mh p_mh(p_i, p_o);

   initial begin
      p_i.x = 1;
      #1;
      // issue #4925
      if (p_o.x != 1'b1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
