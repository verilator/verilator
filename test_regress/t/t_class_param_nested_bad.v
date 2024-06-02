// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Arkadiusz Kozdra.
// SPDX-License-Identifier: CC0-1.0

typedef class Cls;

class Wrap #(parameter P = 13);
   function int get_p;
      return c1.get_p();
   endfunction
   function new;
      c1 = new;
   endfunction
   Cls#(PMINUS1 + 1) c1;
   localparam PMINUS1 = P - 1;  // Checking works when last
endclass

class Wrap2 #(parameter P = 35);
   function int get_p;
      return c1.get_p();
   endfunction
   function new;
      c1 = new;
   endfunction
   Wrap#(PMINUS1 + 1) c1;
   localparam PMINUS1 = P - 1;  // Checking works when last
endclass

class Cls #(parameter PBASE = 12);
   bit [PBASE-1:0] member;
   function bit [PBASE-1:0] get_member;
      return member;
   endfunction
   static function int get_p;
      return PBASE;
   endfunction
   typedef enum { E_PBASE = PBASE } enum_t;
endclass

typedef Cls#(8) Cls8_t;

module t (/*AUTOARG*/);

   Cls c12;
   Cls #(.PBASE(4)) c4;
   Cls8_t c8;
   Wrap #(.P(16)) w16;
   Wrap2 #(.P(32)) w32;
   Wrap2 #(Wrap#(19)::PBASE * 2) w38;
   initial begin
      c12 = new;
      c4 = new;
      c8 = new;
      w16 = new;
      w32 = new;
      w38 = new;
      if (w38.get_p() != 38) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
