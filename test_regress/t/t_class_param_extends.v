// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Code your testbench here
// or browse Examples
class Base #(parameter PBASE = 12);
   bit [PBASE-1:0] member;
  function bit [PBASE-1:0] get_member;
      return member;
   endfunction
   function int get_p;
      return PBASE;
   endfunction
endclass

class Cls #(parameter P = 13) extends Base #(P);
endclass

typedef Cls#(8) Cls8_t;

class Getter1;
   function int get_int;
      return 1;
   endfunction
endclass

class Getter2;
   function int get_int;
      return 2;
   endfunction
endclass

class Foo #(type T=Getter1);
   T foo_field;
   int x;
   function new(int y);
      foo_field = new;
      x = y;
   endfunction
endclass

class Bar #(type S=Getter2) extends Foo#(S);
   T field;
   function new(int y);
      super.new(y);
      field = new;
   endfunction

   function int get_field_int;
      return field.get_int();
   endfunction

   function int get_foo_field_int;
      return foo_field.get_int();
   endfunction
endclass

// See also t_class_param_mod.v

module t (/*AUTOARG*/);

   Cls #(.P(4)) c4;
   Cls8_t c8;
   Bar b;

   initial begin
      c4 = new;
      c8 = new;
      b = new(1);
      if (c4.PBASE != 4) $stop;
      if (c8.PBASE != 8) $stop;
      if (c4.get_p() != 4) $stop;
      if (c8.get_p() != 8) $stop;
      // verilator lint_off WIDTH
      c4.member = 32'haaaaaaaa;
      c8.member = 32'haaaaaaaa;
      // verilator lint_on WIDTH
      if (c4.member != 4'ha) $stop;
      if (c4.get_member() != 4'ha) $stop;
      if (c8.member != 8'haa) $stop;
      if (c8.get_member() != 8'haa) $stop;
      $display("c4 = %s", $sformatf("%p", c4));
      if ($sformatf("%p", c4) != "'{member:'ha}") $stop;

      if (b.x != 1) $stop;
      if (b.get_field_int() != 2) $stop;
      if (b.get_foo_field_int() != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
