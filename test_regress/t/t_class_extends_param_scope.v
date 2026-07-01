// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Sergey Chusov
// SPDX-License-Identifier: CC0-1.0

// A factory-like static method, as used by UVM's type_id::create().
class registry #(type T = int);
  static function T create();
    T r = new;
    return r;
  endfunction
endclass

class item;
  int val;
  typedef registry#(item) type_id;
  function new();
    val = 42;
  endfunction
endclass

class seq_base #(type REQ = int, type RSP = REQ);
  REQ req;
endclass

// Non-parameterized class extending a parameterized base.
// REQ is a type parameter inherited from the (specialized) base class and is
// here used as a '::' class scope: REQ::type_id::create().  Resolving REQ in
// this position requires deferring until after V3Param has bound REQ to item.
class seq extends seq_base #(item);
  function int make();
    REQ r;
    r = REQ::type_id::create();
    return r.val;
  endfunction
endclass

module t;
  seq s;
  initial begin
    s = new;
    if (s.make() != 42) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
