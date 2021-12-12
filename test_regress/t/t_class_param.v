// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls #(parameter P = 12);
   bit [P-1:0] member;
   function bit [P-1:0] get_member;
      return member;
   endfunction
   function int get_p;
      return P;
   endfunction
endclass

typedef Cls#(5) Cls5_t;

module t (/*AUTOARG*/);

   Cls c12;
   Cls #(.P(4)) c4;
   Cls5_t c5;

   initial begin
      c12 = new;
      c4 = new;
      c5 = new;
      if (c12.P != 12) $stop;
      if (c4.P != 4) $stop;
      if (c5.P != 5) $stop;
      if (c12.get_p() != 12) $stop;
      if (c4.get_p() != 4) $stop;
      // verilator lint_off WIDTH
      c12.member = 32'haaaaaaaa;
      c4.member = 32'haaaaaaaa;
      // verilator lint_on WIDTH
      if (c12.member != 12'haaa) $stop;
      if (c4.member != 4'ha) $stop;
      if (c12.get_member() != 12'haaa) $stop;
      if (c4.get_member() != 4'ha) $stop;
      if ($sformatf("%p", c12) != "'{member:'haaa}") $stop;
      if ($sformatf("%p", c4) != "'{member:'ha}") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
