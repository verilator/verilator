// DESCRIPTION: Verilator: Verilog Test module
//
// A data member/variable named identically to a type from an enclosing scope
// must resolve its type specifier against the enclosing-scope type, not against
// the just-declared variable (IEEE 1800-2023 6.18). This is the UVM RAL /
// peakrdl-regblock pattern: 'rand <block_t> <same_name>;'. A reference to the
// type made before such a variable is declared, e.g. as a type parameter, also
// resolves to the type, as the variable is not yet visible (IEEE 1800-2023 6.5).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Tom Jackson
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

typedef logic [7:0] my_t;  // type at $unit scope

class C;
  my_t my_t;  // member named the same as its (outer-scope) type
endclass

class D;
  my_t a;  // second use of the type name after the shadowing variable...
  my_t my_t;  // ... is also legal; both resolve to the $unit typedef
endclass

// The exact RAL shape: class member named after its class type
class my_blk;
  int x;
endclass

class parent;
  rand my_blk my_blk;
endclass

// The type parameter is the class, as the member named the same is declared later
class monitor;
  mailbox #(my_blk) fifo = new();
  my_blk my_blk;
  function void get();
    void'(fifo.try_get(my_blk));
  endfunction
endclass

class Holder #(
    type T = int
);
  T v;
endclass

// Likewise with a base class still to be parameterized
class param_monitor extends Holder #(byte);
  mailbox #(my_blk) fifo = new();
  my_blk my_blk;
endclass

typedef int item_t;  // type at $unit scope, named like the class types below

class base;
  typedef logic [6:0] item_t;
endclass

// The type parameter is the inherited type, as the member named the same is declared later
class derived extends base;
  Holder #(item_t) holder = new;
  int item_t;
endclass

interface class ifc;
  typedef logic [6:0] item_t;
endclass

// Types are not inherited through 'implements' (IEEE 1800-2023 8.26.3), so this is the $unit one
class implementer implements ifc;
  Holder #(item_t) holder = new;
  int item_t;
endclass

class Cls;
endclass

module t;
  my_t my_t;  // also legal at module scope
  mailbox #(my_blk) blk_fifo = new();  // likewise the class at module scope
  my_blk my_blk;

  initial begin
    static C c = new;
    static parent p = new;
    static Cls Cls = new;
    static monitor mon = new;
    static param_monitor pmon = new;
    static derived der = new;
    static implementer imp = new;
    c.my_t = 8'hAB;
    p.my_blk = new;
    p.my_blk.x = 5;
    my_t = 8'h12;
    my_blk = new;
    my_blk.x = 7;
    void'(blk_fifo.try_put(my_blk));
    void'(mon.fifo.try_put(my_blk));
    void'(pmon.fifo.try_put(my_blk));
    mon.get();
    der.holder.v = '1;
    imp.holder.v = '1;
    `checkh(c.my_t, 8'hAB);
    `checkh(p.my_blk.x, 5);
    `checkh(my_t, 8'h12);
    `checkh(blk_fifo.num(), 1);
    `checkh(mon.my_blk.x, 7);
    `checkh(pmon.fifo.num(), 1);
    `checkh(der.holder.v, 7'h7f);
    `checkh(imp.holder.v, 32'hffffffff);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
