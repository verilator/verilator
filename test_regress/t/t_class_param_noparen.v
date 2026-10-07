// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A parameterized class prefix without #() is legal within the scope of that class, including
// its nested classes, where it refers to the enclosing specialization. Elsewhere it is
// non-standard (IEEE 1800-2023 8.25.1), but like other simulators it refers to the default
// specialization.

package pkg;
  class Registry #(
      type T = int
  );
    static function T create(string name);
      T obj = new(name);
      return obj;
    endfunction
  endclass

  class Cls #(
      type T = int,
      int P = 3
  );
    typedef Registry#(Cls#(T, P)) type_id;
    parameter int Q = P + 2;
    static int count;
    string name;
    function new(string name = "");
      this.name = name;
      ++count;
    endfunction
    static function int twice(int x);
      return 2 * x;
    endfunction
    class Inner;
      static function int p();
        return Cls::P;  // Ok, within Cls
      endfunction
    endclass
    static function int innerP();
      return Inner::p();
    endfunction
    typedef Cls this_t;  // Ok, default specialization even here, unlike 'Cls::'
    static function int thisQ();
      return this_t::Q;
    endfunction
  endclass
endpackage

module t;
  import pkg::*;

  class Other extends Cls #();  // Ok
  endclass

  class OtherMaybe extends Cls;  // Questionable but others do not warn
  endclass

  typedef Cls#(shortint, 4) Cls2_t;  // Ok
  typedef Cls ClsNone_t;  // Ok

  class User;
    static function Cls#() make(string name);
      return Cls::type_id::create(name);  // Bad #() required
    endfunction
  endclass

  initial begin
    Cls obj;  // Ok
    Cls2_t other;
    Cls::T value;  // Bad #() required
    int count;
    int p;
    int q;
    int twice;
    string type_id_name;
    string t_name;
    obj = User::make("created");
    other = new("other");
    Cls::count += 10;  // Bad #() required
    count = pkg::Cls::count;  // Bad #() required
    p = Cls::P;  // Bad #() required
    q = Cls::Q;  // Bad #() required
    twice = Cls::twice(21);  // Bad #() required
    type_id_name = $typename(Cls::type_id);  // Bad #() required
    t_name = $typename(Cls::T);  // Bad #() required

    `checks(obj.name, "created");
    `checkd(count, 11);
    `checkd(Cls#()::count, 11);
    `checkd(Cls2_t::count, 1);
    `checkd(p, 3);
    `checkd(q, 5);
    `checkd(Cls#()::Q, 5);
    `checkd(Cls2_t::Q, 6);
    `checkd(ClsNone_t::P, 3);
    `checkd(ClsNone_t::Q, 5);
    ClsNone_t::count += 1;
    `checkd(Cls#()::count, 12);
    `checkd(twice, 42);
    `checks(type_id_name, $typename(Cls#()::type_id));
    `checks(t_name, $typename(Cls#()::T));
    `checks($typename(ClsNone_t::T), $typename(Cls#()::T));
    `checkd($bits(value), 32);
    `checkd(Cls#()::innerP(), 3);
    `checkd(Cls2_t::innerP(), 4);
    `checkd(Cls2_t::thisQ(), 5);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
