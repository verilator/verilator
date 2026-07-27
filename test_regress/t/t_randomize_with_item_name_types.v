// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// IEEE 1800-2023 7.12.1 gives array-method 'with' clauses a default iterator
// named 'item'. randomize() with (18.7) has no such iterator, so a user
// variable named 'item' must resolve normally inside the constraint.

class Payload;
  rand bit [31:0] addr;
endclass

class Other;
  bit [31:0] tag;
endclass

class Seq;
  Other item;  // class member named 'item', of a type with no 'addr'

  function new();
    item = new();
    item.tag = 32'h5a5a_5a5a;
  endfunction

  // Before the fix 'item' bound to the randomize target, so this failed
  // elaboration with "Member 'tag' not found in class 'Payload'".
  function void check_other_type();
    Payload r = new();
    int ok;
    ok = r.randomize() with {addr == item.tag;};
    `checkd(ok, 1)
    `checkh(r.addr, 32'h5a5a_5a5a)
  endfunction

  // Undotted scalar named 'item'. Before the fix this produced C++ that did
  // not compile: "'item' was not declared in this scope".
  function void check_bare_scalar();
    Payload r = new();
    bit [31:0] item = 32'hcafe_f00d;
    int ok;
    ok = r.randomize() with {addr == item;};
    `checkd(ok, 1)
    `checkh(r.addr, 32'hcafe_f00d)
  endfunction
endclass

module t (  /*AUTOARG*/);
  initial begin
    automatic Seq s = new();
    s.check_other_type();
    s.check_bare_scalar();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
