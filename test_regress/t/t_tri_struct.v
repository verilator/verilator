// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Ryszard Rozak.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
   bit x;
} p_struct_t;

typedef struct {
   bit x;
} u_struct_t;

module p_mh (inout p_struct_t p_i, inout p_struct_t p_o);
   // OK: module p_mh (input p_struct_t p_i, output p_struct_t p_o);
   assign p_o.x = p_i.x;
endmodule

module u_mh (inout u_struct_t u_i, inout u_struct_t u_o);
   // OK: module u_mh (input u_struct_t u_i, output u_struct_t u_o);
   assign u_o.x = u_i.x;
endmodule

module t;
   p_struct_t p_i, p_o;
   u_struct_t u_i, u_o;

   p_mh p_mh(p_i, p_o);
   u_mh u_mh(u_i, u_o);

   initial begin
      p_i.x = 1;
      u_i.x = 1;
      #1;
      if (p_o.x != 1'b1) $stop;
      if (u_o.x != 1'b1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
