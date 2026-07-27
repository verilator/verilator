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

  // A queue member named 'item'. The randomize target has no such member, so
  // this must resolve to the caller's queue and index it normally.
  function void check_queue_element();
    Payload r = new();
    bit [31:0] item[$] = '{32'h1111_1111, 32'h2222_2222};
    int ok;
    ok = r.randomize() with {addr == item[1];};
    `checkd(ok, 1)
    `checkh(r.addr, 32'h2222_2222)
  endfunction
endclass

module t (  /*AUTOARG*/);
  // std::randomize() with reaches the 'with' clause through a different call
  // site than a class randomize(), and must not shadow 'item' either.
  function automatic void check_std_randomize();
    bit [31:0] item = 32'h5eed_5eed;
    bit [31:0] v;
    int ok;
    ok = std::randomize(v) with {v == item;};
    `checkd(ok, 1)
    `checkh(v, 32'h5eed_5eed)
  endfunction

  initial begin
    automatic Seq s = new();
    s.check_other_type();
    s.check_bare_scalar();
    s.check_queue_element();
    check_std_randomize();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
