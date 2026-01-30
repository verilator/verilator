// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Foo;
  event write_events[int];

  function void add_event(int index, event in);
    write_events[index] = in;
  endfunction

  task trigger_event(int index);
    ->write_events[index];
  endtask

  function void delete_event(int index);
    write_events.delete(index);
  endfunction
endclass

class Bar;
  Foo foo;
  event baz;

  function new(Foo foo);
    this.foo = foo;
  endfunction

  task go();
    foo.add_event(3, baz);
    @baz;
    $display("got here");
    foo.delete_event(3);
  endtask
endclass

module top;
  Bar bar;
  Foo foo;

  initial begin
    foo = new();
    bar = new(foo);
    bar.go();
  end

  initial begin
    #10;
    foo.trigger_event(3);
    $finish;
  end

endmodule
