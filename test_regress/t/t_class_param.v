// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

// See also t_class_param_mod.v

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
   initial begin
      c12 = new;
      c4 = new;
      c8 = new;
      w16 = new;
      w32 = new;
      if (Cls#()::PBASE != 12) $stop;
      if (Cls#(4)::PBASE != 4) $stop;
      if (Cls8_t::PBASE != 8) $stop;

      if (Cls#()::E_PBASE != 12) $stop;
      if (Cls#(4)::E_PBASE != 4) $stop;
      if (Cls8_t::E_PBASE != 8) $stop;

      if (c12.PBASE != 12) $stop;
      if (c4.PBASE != 4) $stop;
      if (c8.PBASE != 8) $stop;

      if (Cls#()::get_p() != 12) $stop;
      if (Cls#(4)::get_p() != 4) $stop;
      if (Cls8_t::get_p() != 8) $stop;

      if (c12.get_p() != 12) $stop;
      if (c4.get_p() != 4) $stop;
      if (c8.get_p() != 8) $stop;
      if (w16.get_p() != 16) $stop;
      if (w32.get_p() != 32) $stop;

      // verilator lint_off WIDTH
      c12.member = 32'haaaaaaaa;
      c4.member = 32'haaaaaaaa;
      c8.member = 32'haaaaaaaa;
      // verilator lint_on WIDTH
      if (c12.member != 12'haaa) $stop;
      if (c4.member != 4'ha) $stop;
      if (c12.get_member() != 12'haaa) $stop;
      if (c4.get_member() != 4'ha) $stop;
      `checks($sformatf("%p", c12), "'{member:'haaa}");
      `checks($sformatf("%p", c4), "'{member:'ha}");

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
