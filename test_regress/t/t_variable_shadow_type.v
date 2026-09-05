// DESCRIPTION: Verilator: Verilog Test module
//
// A data member/variable named identically to a type from an enclosing scope
// must resolve its type specifier against the enclosing-scope type, not against
// the just-declared variable (IEEE 1800-2023 6.18). This is the UVM RAL /
// peakrdl-regblock pattern: 'rand <block_t> <same_name>;'.
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

class Cls;
endclass

module t;
  my_t my_t;  // also legal at module scope

  initial begin
    static C c = new;
    static parent p = new;
    static Cls Cls = new;
    c.my_t = 8'hAB;
    p.my_blk = new;
    p.my_blk.x = 5;
    my_t = 8'h12;
    `checkh(c.my_t, 8'hAB);
    `checkh(p.my_blk.x, 5);
    `checkh(my_t, 8'h12);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
