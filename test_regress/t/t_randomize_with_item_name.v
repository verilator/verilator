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

class Seq;
  Payload item;  // class member deliberately named 'item'

  function new();
    item = new();
    item.addr = 32'h8000_0084;
  endfunction

  // Member handle named 'item', dereferenced in the constraint.
  function void check_member_handle();
    Payload r = new();
    int ok;
    ok = r.randomize() with {addr == item.addr;};
    `checkd(ok, 1)
    `checkh(r.addr, 32'h8000_0084)
  endfunction

  // Same, but not a tautology even when misbound. Before the fix this became
  // 'addr == addr + 1' and randomize() returned 0.
  function void check_not_tautology();
    Payload r = new();
    int ok;
    ok = r.randomize() with {addr == item.addr + 1;};
    `checkd(ok, 1)
    `checkh(r.addr, 32'h8000_0085)
  endfunction


  // A local, rather than a member, also named 'item'.
  function void check_local_handle();
    Payload r = new();
    Payload item = new();
    int ok;
    item.addr = 32'hdead_beef;
    ok = r.randomize() with {addr == item.addr;};
    `checkd(ok, 1)
    `checkh(r.addr, 32'hdead_beef)
  endfunction


  // The array-method iterator must keep working, in a class that also has a
  // variable named 'item'. This is what the name exists for.
  function void check_array_method_iterator();
    int q[$] = '{1, 4, 2, 7};
    int found[$];
    found = q.find with (item > 3);
    `checkd(found.size(), 2)
    `checkd(found[0], 4)
    `checkd(found[1], 7)
  endfunction
endclass

module t (  /*AUTOARG*/);
  initial begin
    automatic Seq s = new();
    s.check_member_handle();
    s.check_not_tautology();
    s.check_local_handle();
    s.check_array_method_iterator();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
