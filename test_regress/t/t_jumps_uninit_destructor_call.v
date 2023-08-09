// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0
class Foo;
  string arra[2];
  string arrb[string];

  function new();
    arra = '{"baz", "boo"};
    arrb = '{"baz": "inga!", "boo": "..."};
  endfunction

  task automatic return_before_fork(bit b);
    if (b) begin
      // This is going to translate to a `goto` statement.
      return;
    end
    // This will instantiate a `VlForkSync` object (local to the call, as we are under a class)
    fork
      #10 $display("forked process");
    join
    // This is where we jump to from the aforementioned goto. If we don't wrap the `VlForkSync`
    // object in a scope that ends before that point, we will end up calling its destructor
    // without having it initialized first.
  endtask
  task automatic return_before_select(bit b, int idx);
    if (b) return; // goto
    // This will create two temporary strings used to select from `arrb` and assign to it.
    arrb[arra[idx]] = #10 "yah!";
    // jump here
  endtask
endclass

module t();
  initial begin
    Foo foo;
    foo = new;
    foo.return_before_fork(1'b1);
    foo.return_before_select(1'b1, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
