// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
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
    localparam int Q = P + 2;
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
        return Cls::P;
      endfunction
    endclass
    static function int innerP();
      return Inner::p();
    endfunction
  endclass
endpackage

module t;
  import pkg::*;

  class User;
    static function Cls#() make(string name);
      // verilator lint_off NONSTD
      return Cls::type_id::create(name);
      // verilator lint_on NONSTD
    endfunction
  endclass

  initial begin
    Cls #() obj;
    Cls #(shortint, 4) other;
    // verilator lint_off NONSTD
    Cls::T value;
    obj = User::make("created");
    Cls::count += 10;
    `checkd(Cls::count, 11);
    `checkd(pkg::Cls::count, 11);
    `checkd(Cls::P, 3);
    `checkd(Cls::Q, 5);
    `checkd(Cls::twice(21), 42);
    `checks($typename(Cls::type_id), $typename(Cls#()::type_id));
    `checks($typename(Cls::T), $typename(Cls#()::T));
    // verilator lint_on NONSTD
    other = new("other");
    `checks(obj.name, "created");
    `checkd(Cls#()::count, 11);
    `checkd(Cls#(shortint, 4)::count, 1);
    `checkd($bits(value), 32);
    `checkd(Cls#()::innerP(), 3);
    `checkd(Cls#(shortint, 4)::innerP(), 4);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
