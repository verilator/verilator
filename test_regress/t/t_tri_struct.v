// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

typedef struct {
   bit x;
} u_struct_t;

module u_mh (inout u_struct_t u_i, inout u_struct_t u_o);
   assign u_o.x = u_i.x;
endmodule

module t;
   u_struct_t u_i, u_o;

   u_mh u_mh(u_i, u_o);

   initial begin
      u_i.x = 1;
      #1;
      if (u_o.x != 1'b1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
