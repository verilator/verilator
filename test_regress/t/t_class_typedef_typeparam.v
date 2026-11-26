// DESCRIPTION: Verilator: Verilog Test module
//
// A typedef names a specialization of a parameterized class. That typedef's
// type parameter is then used as a type: directly as a type argument, through
// a second typedef, and as a named parameter pin. The widths are not powers of
// two, and several specializations of the same class are declared in the
// reverse of the order they are used, so each typedef's T must come from its
// own specialization and not the template's default or another specialization.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Olivier DArcy
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class holder #(
    type T = bit
);
endclass

class box #(
    type T = logic,
    type ITEM = holder#(bit)
);
  T storage;
endclass

module t;
  typedef holder#(logic [6:0]) holder_t;
  typedef holder#(logic [12:0]) wide_holder_t;
  typedef holder#() default_holder_t;

  // The typedef's type parameter, used directly as a type argument.
  typedef box#(holder_t::T, holder_t) box_direct_t;
  // Named first, then used as a type argument.
  typedef holder_t::T value_t;
  typedef box#(value_t, holder_t) box_alias_t;
  // Same reference as a named parameter pin.
  typedef box#(.T(holder_t::T), .ITEM(holder_t)) box_pin_t;
  // Specializations declared widest first, used narrowest first.
  typedef box#(wide_holder_t::T) box_wide_t;
  typedef box#(holder_t::T) box_narrow_t;
  // The class parameter keeps its default.
  typedef box#(default_holder_t::T) box_default_t;

  initial begin
    begin
      box_direct_t direct;
      direct = new;
      `checkd($bits(direct.storage), 7);
      direct.storage = 7'h55;
      `checkh(direct.storage, 7'h55);
    end

    begin
      box_alias_t aliasb;
      aliasb = new;
      `checkd($bits(aliasb.storage), 7);
      aliasb.storage = 7'h2A;
      `checkh(aliasb.storage, 7'h2A);
    end

    begin
      box_pin_t pin;
      pin = new;
      `checkd($bits(pin.storage), 7);
      pin.storage = 7'h3C;
      `checkh(pin.storage, 7'h3C);
    end

    begin
      box_narrow_t narrow;
      box_wide_t wide;
      narrow = new;
      wide = new;
      `checkd($bits(narrow.storage), 7);
      `checkd($bits(wide.storage), 13);
      wide.storage = 13'h1A5A;
      `checkh(wide.storage, 13'h1A5A);
    end

    begin
      box_default_t dflt;
      dflt = new;
      `checkd($bits(dflt.storage), 1);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
