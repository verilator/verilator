// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// See also t_class_param.v

module t (/*AUTOARG*/);

class Cls #(parameter P = 12);
   bit [P-1:0] member;
   function bit [P-1:0] get_member;
      return member;
   endfunction
   function int get_p;
      return P;
   endfunction
endclass

class Wrap #(parameter PMINUS1 = 3);
   localparam P = PMINUS1 + 1;
   Cls#(P) c1;
   function int get_p;
      return c1.get_p();
   endfunction
endclass

   typedef Cls#(5) Cls5_t;

   Cls c12;
   Cls #(.P(4)) c4;
   Cls5_t c5;
   Wrap #(.PMINUS1(15)) w16;
  
   initial begin
      c12 = new;
      c4 = new;
      c5 = new;
      w16 = new;
      if (c12.P != 12) $stop;
      if (c4.P != 4) $stop;
      if (c5.P != 5) $stop;
      if (c12.get_p() != 12) $stop;
      if (c4.get_p() != 4) $stop;
      if (c5.get_p() != 5) $stop;
      if (w16.get_p() != 16) $stop;
      // verilator lint_off WIDTH
      c12.member = 32'haaaaaaaa;
      c4.member = 32'haaaaaaaa;
      c5.member = 32'haaaaaaaa;
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
